pub mod on_unimplemented;
pub mod suggestions;

use super::{
    FulfillmentContext, FulfillmentError, FulfillmentErrorCode, MismatchedProjectionTypes,
    Obligation, ObligationCause, ObligationCauseCode, OnUnimplementedDirective,
    OnUnimplementedNote, OutputTypeParameterMismatch, Overflow, PredicateObligation,
    SelectionContext, SelectionError, TraitNotObjectSafe,
};

use crate::infer::error_reporting::{TyCategory, TypeAnnotationNeeded as ErrorCode};
use crate::infer::type_variable::{TypeVariableOrigin, TypeVariableOriginKind};
use crate::infer::{self, InferCtxt, TyCtxtInferExt};
use rustc_data_structures::fx::FxHashMap;
use rustc_errors::{
    pluralize, struct_span_err, Applicability, Diagnostic, DiagnosticBuilder, ErrorGuaranteed,
    MultiSpan, Style,
};
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_hir::intravisit::Visitor;
use rustc_hir::GenericParam;
use rustc_hir::Item;
use rustc_hir::Node;
use rustc_infer::infer::error_reporting::TypeErrCtxt;
use rustc_infer::infer::TypeTrace;
use rustc_infer::traits::TraitEngine;
use rustc_middle::traits::select::OverflowError;
use rustc_middle::ty::abstract_const::NotConstEvaluatable;
use rustc_middle::ty::error::ExpectedFound;
use rustc_middle::ty::fold::{TypeFolder, TypeSuperFoldable};
use rustc_middle::ty::{
    self, SubtypePredicate, ToPolyTraitRef, ToPredicate, TraitRef, Ty, TyCtxt, TypeFoldable,
    TypeVisitable,
};
use rustc_session::Limit;
use rustc_span::def_id::LOCAL_CRATE;
use rustc_span::symbol::{kw, sym};
use rustc_span::{ExpnKind, Span, DUMMY_SP};
use std::fmt;
use std::iter;
use std::ops::ControlFlow;

use crate::traits::query::evaluate_obligation::InferCtxtExt as _;
use crate::traits::query::normalize::AtExt as _;
use crate::traits::specialize::to_pretty_impl_header;
use on_unimplemented::TypeErrCtxtExt as _;
use suggestions::TypeErrCtxtExt as _;

pub use rustc_infer::traits::error_reporting::*;

// When outputting impl candidates, prefer showing those that are more similar.
//
// We also compare candidates after skipping lifetimes, which has a lower
// priority than exact matches.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CandidateSimilarity {
    Exact { ignoring_lifetimes: bool },
    Fuzzy { ignoring_lifetimes: bool },
}

#[derive(Debug, Clone, Copy)]
pub struct ImplCandidate<'tcx> {
    pub trait_ref: ty::TraitRef<'tcx>,
    pub similarity: CandidateSimilarity,
}

pub trait InferCtxtExt<'tcx> {
    /// Given some node representing a fn-like thing in the HIR map,
    /// returns a span and `ArgKind` information that describes the
    /// arguments it expects. This can be supplied to
    /// `report_arg_count_mismatch`.
    fn get_fn_like_arguments(&self, node: Node<'_>) -> Option<(Span, Vec<ArgKind>)>;

    /// Reports an error when the number of arguments needed by a
    /// trait match doesn't match the number that the expression
    /// provides.
    fn report_arg_count_mismatch(
        &self,
        span: Span,
        found_span: Option<Span>,
        expected_args: Vec<ArgKind>,
        found_args: Vec<ArgKind>,
        is_closure: bool,
    ) -> DiagnosticBuilder<'tcx, ErrorGuaranteed>;

    /// Checks if the type implements one of `Fn`, `FnMut`, or `FnOnce`
    /// in that order, and returns the generic type corresponding to the
    /// argument of that trait (corresponding to the closure arguments).
    fn type_implements_fn_trait(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        ty: ty::Binder<'tcx, Ty<'tcx>>,
        constness: ty::BoundConstness,
        polarity: ty::ImplPolarity,
    ) -> Result<(ty::ClosureKind, ty::Binder<'tcx, Ty<'tcx>>), ()>;
}

pub trait TypeErrCtxtExt<'tcx> {
    fn report_fulfillment_errors(
        &self,
        errors: &[FulfillmentError<'tcx>],
        body_id: Option<hir::BodyId>,
        fallback_has_occurred: bool,
    ) -> ErrorGuaranteed;

    fn report_overflow_error<T>(
        &self,
        obligation: &Obligation<'tcx, T>,
        suggest_increasing_limit: bool,
    ) -> !
    where
        T: fmt::Display + TypeFoldable<'tcx>;

    fn suggest_new_overflow_limit(&self, err: &mut Diagnostic);

    fn report_overflow_error_cycle(&self, cycle: &[PredicateObligation<'tcx>]) -> !;

    /// The `root_obligation` parameter should be the `root_obligation` field
    /// from a `FulfillmentError`. If no `FulfillmentError` is available,
    /// then it should be the same as `obligation`.
    fn report_selection_error(
        &self,
        obligation: PredicateObligation<'tcx>,
        root_obligation: &PredicateObligation<'tcx>,
        error: &SelectionError<'tcx>,
        fallback_has_occurred: bool,
    );
}

impl<'tcx> InferCtxtExt<'tcx> for InferCtxt<'tcx> {
    /// Given some node representing a fn-like thing in the HIR map,
    /// returns a span and `ArgKind` information that describes the
    /// arguments it expects. This can be supplied to
    /// `report_arg_count_mismatch`.
    fn get_fn_like_arguments(&self, node: Node<'_>) -> Option<(Span, Vec<ArgKind>)> {
        let sm = self.tcx.sess.source_map();
        let hir = self.tcx.hir();
        Some(match node {
            Node::Expr(&hir::Expr {
                kind: hir::ExprKind::Closure(&hir::Closure { body, fn_decl_span, .. }),
                ..
            }) => (
                fn_decl_span,
                hir.body(body)
                    .params
                    .iter()
                    .map(|arg| {
                        if let hir::Pat { kind: hir::PatKind::Tuple(ref args, _), span, .. } =
                            *arg.pat
                        {
                            Some(ArgKind::Tuple(
                                Some(span),
                                args.iter()
                                    .map(|pat| {
                                        sm.span_to_snippet(pat.span)
                                            .ok()
                                            .map(|snippet| (snippet, "_".to_owned()))
                                    })
                                    .collect::<Option<Vec<_>>>()?,
                            ))
                        } else {
                            let name = sm.span_to_snippet(arg.pat.span).ok()?;
                            Some(ArgKind::Arg(name, "_".to_owned()))
                        }
                    })
                    .collect::<Option<Vec<ArgKind>>>()?,
            ),
            Node::Item(&hir::Item { kind: hir::ItemKind::Fn(ref sig, ..), .. })
            | Node::ImplItem(&hir::ImplItem { kind: hir::ImplItemKind::Fn(ref sig, _), .. })
            | Node::TraitItem(&hir::TraitItem {
                kind: hir::TraitItemKind::Fn(ref sig, _), ..
            }) => (
                sig.span,
                sig.decl
                    .inputs
                    .iter()
                    .map(|arg| match arg.kind {
                        hir::TyKind::Tup(ref tys) => ArgKind::Tuple(
                            Some(arg.span),
                            vec![("_".to_owned(), "_".to_owned()); tys.len()],
                        ),
                        _ => ArgKind::empty(),
                    })
                    .collect::<Vec<ArgKind>>(),
            ),
            Node::Ctor(ref variant_data) => {
                let span = variant_data.ctor_hir_id().map_or(DUMMY_SP, |id| hir.span(id));
                (span, vec![ArgKind::empty(); variant_data.fields().len()])
            }
            _ => panic!("non-FnLike node found: {:?}", node),
        })
    }

    /// Reports an error when the number of arguments needed by a
    /// trait match doesn't match the number that the expression
    /// provides.
    fn report_arg_count_mismatch(
        &self,
        span: Span,
        found_span: Option<Span>,
        expected_args: Vec<ArgKind>,
        found_args: Vec<ArgKind>,
        is_closure: bool,
    ) -> DiagnosticBuilder<'tcx, ErrorGuaranteed> {
        let kind = if is_closure { "closure" } else { "function" };

        let args_str = |arguments: &[ArgKind], other: &[ArgKind]| {
            let arg_length = arguments.len();
            let distinct = matches!(other, &[ArgKind::Tuple(..)]);
            match (arg_length, arguments.get(0)) {
                (1, Some(&ArgKind::Tuple(_, ref fields))) => {
                    format!("a single {}-tuple as argument", fields.len())
                }
                _ => format!(
                    "{} {}argument{}",
                    arg_length,
                    if distinct && arg_length > 1 { "distinct " } else { "" },
                    pluralize!(arg_length)
                ),
            }
        };

        let expected_str = args_str(&expected_args, &found_args);
        let found_str = args_str(&found_args, &expected_args);

        let mut err = struct_span_err!(
            self.tcx.sess,
            span,
            E0593,
            "{} is expected to take {}, but it takes {}",
            kind,
            expected_str,
            found_str,
        );

        err.span_label(span, format!("expected {} that takes {}", kind, expected_str));

        if let Some(found_span) = found_span {
            err.span_label(found_span, format!("takes {}", found_str));

            // move |_| { ... }
            // ^^^^^^^^-- def_span
            //
            // move |_| { ... }
            // ^^^^^-- prefix
            let prefix_span = self.tcx.sess.source_map().span_until_non_whitespace(found_span);
            // move |_| { ... }
            //      ^^^-- pipe_span
            let pipe_span =
                if let Some(span) = found_span.trim_start(prefix_span) { span } else { found_span };

            // Suggest to take and ignore the arguments with expected_args_length `_`s if
            // found arguments is empty (assume the user just wants to ignore args in this case).
            // For example, if `expected_args_length` is 2, suggest `|_, _|`.
            if found_args.is_empty() && is_closure {
                let underscores = vec!["_"; expected_args.len()].join(", ");
                err.span_suggestion_verbose(
                    pipe_span,
                    &format!(
                        "consider changing the closure to take and ignore the expected argument{}",
                        pluralize!(expected_args.len())
                    ),
                    format!("|{}|", underscores),
                    Applicability::MachineApplicable,
                );
            }

            if let &[ArgKind::Tuple(_, ref fields)] = &found_args[..] {
                if fields.len() == expected_args.len() {
                    let sugg = fields
                        .iter()
                        .map(|(name, _)| name.to_owned())
                        .collect::<Vec<String>>()
                        .join(", ");
                    err.span_suggestion_verbose(
                        found_span,
                        "change the closure to take multiple arguments instead of a single tuple",
                        format!("|{}|", sugg),
                        Applicability::MachineApplicable,
                    );
                }
            }
            if let &[ArgKind::Tuple(_, ref fields)] = &expected_args[..]
                && fields.len() == found_args.len()
                && is_closure
            {
                let sugg = format!(
                    "|({}){}|",
                    found_args
                        .iter()
                        .map(|arg| match arg {
                            ArgKind::Arg(name, _) => name.to_owned(),
                            _ => "_".to_owned(),
                        })
                        .collect::<Vec<String>>()
                        .join(", "),
                    // add type annotations if available
                    if found_args.iter().any(|arg| match arg {
                        ArgKind::Arg(_, ty) => ty != "_",
                        _ => false,
                    }) {
                        format!(
                            ": ({})",
                            fields
                                .iter()
                                .map(|(_, ty)| ty.to_owned())
                                .collect::<Vec<String>>()
                                .join(", ")
                        )
                    } else {
                        String::new()
                    },
                );
                err.span_suggestion_verbose(
                    found_span,
                    "change the closure to accept a tuple instead of individual arguments",
                    sugg,
                    Applicability::MachineApplicable,
                );
            }
        }

        err
    }

    fn type_implements_fn_trait(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        ty: ty::Binder<'tcx, Ty<'tcx>>,
        constness: ty::BoundConstness,
        polarity: ty::ImplPolarity,
    ) -> Result<(ty::ClosureKind, ty::Binder<'tcx, Ty<'tcx>>), ()> {
        self.commit_if_ok(|_| {
            for trait_def_id in [
                self.tcx.lang_items().fn_trait(),
                self.tcx.lang_items().fn_mut_trait(),
                self.tcx.lang_items().fn_once_trait(),
            ] {
                let Some(trait_def_id) = trait_def_id else { continue };
                // Make a fresh inference variable so we can determine what the substitutions
                // of the trait are.
                let var = self.next_ty_var(TypeVariableOrigin {
                    span: DUMMY_SP,
                    kind: TypeVariableOriginKind::MiscVariable,
                });
                let substs = self.tcx.mk_substs_trait(ty.skip_binder(), &[var.into()]);
                let obligation = Obligation::new(
                    ObligationCause::dummy(),
                    param_env,
                    ty.rebind(ty::TraitPredicate {
                        trait_ref: ty::TraitRef::new(trait_def_id, substs),
                        constness,
                        polarity,
                    })
                    .to_predicate(self.tcx),
                );
                let mut fulfill_cx = FulfillmentContext::new_in_snapshot();
                fulfill_cx.register_predicate_obligation(self, obligation);
                if fulfill_cx.select_all_or_error(self).is_empty() {
                    return Ok((
                        ty::ClosureKind::from_def_id(self.tcx, trait_def_id)
                            .expect("expected to map DefId to ClosureKind"),
                        ty.rebind(self.resolve_vars_if_possible(var)),
                    ));
                }
            }

            Err(())
        })
    }
}
impl<'tcx> TypeErrCtxtExt<'tcx> for TypeErrCtxt<'_, 'tcx> {
    fn report_fulfillment_errors(
        &self,
        errors: &[FulfillmentError<'tcx>],
        body_id: Option<hir::BodyId>,
        fallback_has_occurred: bool,
    ) -> ErrorGuaranteed {
        #[derive(Debug)]
        struct ErrorDescriptor<'tcx> {
            predicate: ty::Predicate<'tcx>,
            index: Option<usize>, // None if this is an old error
        }

        let mut error_map: FxHashMap<_, Vec<_>> = self
            .reported_trait_errors
            .borrow()
            .iter()
            .map(|(&span, predicates)| {
                (
                    span,
                    predicates
                        .iter()
                        .map(|&predicate| ErrorDescriptor { predicate, index: None })
                        .collect(),
                )
            })
            .collect();

        for (index, error) in errors.iter().enumerate() {
            // We want to ignore desugarings here: spans are equivalent even
            // if one is the result of a desugaring and the other is not.
            let mut span = error.obligation.cause.span;
            let expn_data = span.ctxt().outer_expn_data();
            if let ExpnKind::Desugaring(_) = expn_data.kind {
                span = expn_data.call_site;
            }

            error_map.entry(span).or_default().push(ErrorDescriptor {
                predicate: error.obligation.predicate,
                index: Some(index),
            });

            self.reported_trait_errors
                .borrow_mut()
                .entry(span)
                .or_default()
                .push(error.obligation.predicate);
        }

        // We do this in 2 passes because we want to display errors in order, though
        // maybe it *is* better to sort errors by span or something.
        let mut is_suppressed = vec![false; errors.len()];
        for (_, error_set) in error_map.iter() {
            // We want to suppress "duplicate" errors with the same span.
            for error in error_set {
                if let Some(index) = error.index {
                    // Suppress errors that are either:
                    // 1) strictly implied by another error.
                    // 2) implied by an error with a smaller index.
                    for error2 in error_set {
                        if error2.index.map_or(false, |index2| is_suppressed[index2]) {
                            // Avoid errors being suppressed by already-suppressed
                            // errors, to prevent all errors from being suppressed
                            // at once.
                            continue;
                        }

                        if self.error_implies(error2.predicate, error.predicate)
                            && !(error2.index >= error.index
                                && self.error_implies(error.predicate, error2.predicate))
                        {
                            info!("skipping {:?} (implied by {:?})", error, error2);
                            is_suppressed[index] = true;
                            break;
                        }
                    }
                }
            }
        }

        for (error, suppressed) in iter::zip(errors, is_suppressed) {
            if !suppressed {
                self.report_fulfillment_error(error, body_id, fallback_has_occurred);
            }
        }

        self.tcx.sess.delay_span_bug(DUMMY_SP, "expected fullfillment errors")
    }

    /// Reports that an overflow has occurred and halts compilation. We
    /// halt compilation unconditionally because it is important that
    /// overflows never be masked -- they basically represent computations
    /// whose result could not be truly determined and thus we can't say
    /// if the program type checks or not -- and they are unusual
    /// occurrences in any case.
    fn report_overflow_error<T>(
        &self,
        obligation: &Obligation<'tcx, T>,
        suggest_increasing_limit: bool,
    ) -> !
    where
        T: fmt::Display + TypeFoldable<'tcx>,
    {
        let predicate = self.resolve_vars_if_possible(obligation.predicate.clone());
        let mut err = struct_span_err!(
            self.tcx.sess,
            obligation.cause.span,
            E0275,
            "overflow evaluating the requirement `{}`",
            predicate
        );

        if suggest_increasing_limit {
            self.suggest_new_overflow_limit(&mut err);
        }

        self.note_obligation_cause_code(
            &mut err,
            &obligation.predicate,
            obligation.param_env,
            obligation.cause.code(),
            &mut vec![],
            &mut Default::default(),
        );

        err.emit();
        self.tcx.sess.abort_if_errors();
        bug!();
    }

    fn suggest_new_overflow_limit(&self, err: &mut Diagnostic) {
        let suggested_limit = match self.tcx.recursion_limit() {
            Limit(0) => Limit(2),
            limit => limit * 2,
        };
        err.help(&format!(
            "consider increasing the recursion limit by adding a \
             `#![recursion_limit = \"{}\"]` attribute to your crate (`{}`)",
            suggested_limit,
            self.tcx.crate_name(LOCAL_CRATE),
        ));
    }

    /// Reports that a cycle was detected which led to overflow and halts
    /// compilation. This is equivalent to `report_overflow_error` except
    /// that we can give a more helpful error message (and, in particular,
    /// we do not suggest increasing the overflow limit, which is not
    /// going to help).
    fn report_overflow_error_cycle(&self, cycle: &[PredicateObligation<'tcx>]) -> ! {
        let cycle = self.resolve_vars_if_possible(cycle.to_owned());
        assert!(!cycle.is_empty());

        debug!(?cycle, "report_overflow_error_cycle");

        // The 'deepest' obligation is most likely to have a useful
        // cause 'backtrace'
        self.report_overflow_error(cycle.iter().max_by_key(|p| p.recursion_depth).unwrap(), false);
    }

    fn report_selection_error(
        &self,
        mut obligation: PredicateObligation<'tcx>,
        root_obligation: &PredicateObligation<'tcx>,
        error: &SelectionError<'tcx>,
        fallback_has_occurred: bool,
    ) {
        self.set_tainted_by_errors();
        let tcx = self.tcx;
        let mut span = obligation.cause.span;

        let mut err = match *error {
            SelectionError::Ambiguous(ref impls) => {
                let mut err = self.tcx.sess.struct_span_err(
                    obligation.cause.span,
                    &format!("multiple applicable `impl`s for `{}`", obligation.predicate),
                );
                self.annotate_source_of_ambiguity(&mut err, impls, obligation.predicate);
                err.emit();
                return;
            }
            SelectionError::Unimplemented => {
                // If this obligation was generated as a result of well-formedness checking, see if we
                // can get a better error message by performing HIR-based well-formedness checking.
                if let ObligationCauseCode::WellFormed(Some(wf_loc)) =
                    root_obligation.cause.code().peel_derives()
                {
                    if let Some(cause) = self
                        .tcx
                        .diagnostic_hir_wf_check((tcx.erase_regions(obligation.predicate), *wf_loc))
                    {
                        obligation.cause = cause.clone();
                        span = obligation.cause.span;
                    }
                }
                if let ObligationCauseCode::CompareImplItemObligation {
                    impl_item_def_id,
                    trait_item_def_id,
                    kind: _,
                } = *obligation.cause.code()
                {
                    self.report_extra_impl_obligation(
                        span,
                        impl_item_def_id,
                        trait_item_def_id,
                        &format!("`{}`", obligation.predicate),
                    )
                    .emit();
                    return;
                }

                let bound_predicate = obligation.predicate.kind();
                match bound_predicate.skip_binder() {
                    ty::PredicateKind::Trait(trait_predicate) => {
                        let trait_predicate = bound_predicate.rebind(trait_predicate);
                        let mut trait_predicate = self.resolve_vars_if_possible(trait_predicate);

                        trait_predicate.remap_constness_diag(obligation.param_env);
                        let predicate_is_const = ty::BoundConstness::ConstIfConst
                            == trait_predicate.skip_binder().constness;

                        if self.tcx.sess.has_errors().is_some()
                            && trait_predicate.references_error()
                        {
                            return;
                        }
                        let trait_ref = trait_predicate.to_poly_trait_ref();
                        let (post_message, pre_message, type_def) = self
                            .get_parent_trait_ref(obligation.cause.code())
                            .map(|(t, s)| {
                                (
                                    format!(" in `{}`", t),
                                    format!("within `{}`, ", t),
                                    s.map(|s| (format!("within this `{}`", t), s)),
                                )
                            })
                            .unwrap_or_default();

                        let OnUnimplementedNote {
                            message,
                            label,
                            note,
                            parent_label,
                            append_const_msg,
                        } = self.on_unimplemented_note(trait_ref, &obligation);
                        let have_alt_message = message.is_some() || label.is_some();
                        let is_try_conversion = self.is_try_conversion(span, trait_ref.def_id());
                        let is_unsize =
                            Some(trait_ref.def_id()) == self.tcx.lang_items().unsize_trait();
                        let (message, note, append_const_msg) = if is_try_conversion {
                            (
                                Some(format!(
                                    "`?` couldn't convert the error to `{}`",
                                    trait_ref.skip_binder().self_ty(),
                                )),
                                Some(
                                    "the question mark operation (`?`) implicitly performs a \
                                     conversion on the error value using the `From` trait"
                                        .to_owned(),
                                ),
                                Some(None),
                            )
                        } else {
                            (message, note, append_const_msg)
                        };

                        let mut err = struct_span_err!(
                            self.tcx.sess,
                            span,
                            E0277,
                            "{}",
                            message
                                .and_then(|cannot_do_this| {
                                    match (predicate_is_const, append_const_msg) {
                                        // do nothing if predicate is not const
                                        (false, _) => Some(cannot_do_this),
                                        // suggested using default post message
                                        (true, Some(None)) => {
                                            Some(format!("{cannot_do_this} in const contexts"))
                                        }
                                        // overridden post message
                                        (true, Some(Some(post_message))) => {
                                            Some(format!("{cannot_do_this}{post_message}"))
                                        }
                                        // fallback to generic message
                                        (true, None) => None,
                                    }
                                })
                                .unwrap_or_else(|| format!(
                                    "the trait bound `{}` is not satisfied{}",
                                    trait_predicate, post_message,
                                ))
                        );

                        if is_try_conversion {
                            let none_error = self
                                .tcx
                                .get_diagnostic_item(sym::none_error)
                                .map(|def_id| tcx.type_of(def_id));
                            let should_convert_option_to_result =
                                Some(trait_ref.skip_binder().substs.type_at(1)) == none_error;
                            let should_convert_result_to_option =
                                Some(trait_ref.self_ty().skip_binder()) == none_error;
                            if should_convert_option_to_result {
                                err.span_suggestion_verbose(
                                    span.shrink_to_lo(),
                                    "consider converting the `Option<T>` into a `Result<T, _>` \
                                     using `Option::ok_or` or `Option::ok_or_else`",
                                    ".ok_or_else(|| /* error value */)",
                                    Applicability::HasPlaceholders,
                                );
                            } else if should_convert_result_to_option {
                                err.span_suggestion_verbose(
                                    span.shrink_to_lo(),
                                    "consider converting the `Result<T, _>` into an `Option<T>` \
                                     using `Result::ok`",
                                    ".ok()",
                                    Applicability::MachineApplicable,
                                );
                            }
                            if let Some(ret_span) = self.return_type_span(&obligation) {
                                err.span_label(
                                    ret_span,
                                    &format!(
                                        "expected `{}` because of this",
                                        trait_ref.skip_binder().self_ty()
                                    ),
                                );
                            }
                        }

                        if Some(trait_ref.def_id()) == tcx.lang_items().drop_trait()
                            && predicate_is_const
                        {
                            err.note("`~const Drop` was renamed to `~const Destruct`");
                            err.note("See <https://github.com/rust-lang/rust/pull/94901> for more details");
                        }

                        let explanation = if let ObligationCauseCode::MainFunctionType =
                            obligation.cause.code()
                        {
                            "consider using `()`, or a `Result`".to_owned()
                        } else {
                            let ty_desc = match trait_ref.skip_binder().self_ty().kind() {
                                ty::FnDef(_, _) => Some("fn item"),
                                ty::Closure(_, _) => Some("closure"),
                                _ => None,
                            };

                            match ty_desc {
                                Some(desc) => format!(
                                    "{}the trait `{}` is not implemented for {} `{}`",
                                    pre_message,
                                    trait_predicate.print_modifiers_and_trait_path(),
                                    desc,
                                    trait_ref.skip_binder().self_ty(),
                                ),
                                None => format!(
                                    "{}the trait `{}` is not implemented for `{}`",
                                    pre_message,
                                    trait_predicate.print_modifiers_and_trait_path(),
                                    trait_ref.skip_binder().self_ty(),
                                ),
                            }
                        };

                        if self.suggest_add_reference_to_arg(
                            &obligation,
                            &mut err,
                            trait_predicate,
                            have_alt_message,
                        ) {
                            self.note_obligation_cause(&mut err, &obligation);
                            err.emit();
                            return;
                        }
                        if let Some(ref s) = label {
                            // If it has a custom `#[rustc_on_unimplemented]`
                            // error message, let's display it as the label!
                            err.span_label(span, s);
                            if !matches!(trait_ref.skip_binder().self_ty().kind(), ty::Param(_)) {
                                // When the self type is a type param We don't need to "the trait
                                // `std::marker::Sized` is not implemented for `T`" as we will point
                                // at the type param with a label to suggest constraining it.
                                err.help(&explanation);
                            }
                        } else {
                            err.span_label(span, explanation);
                        }

                        if let ObligationCauseCode::ObjectCastObligation(concrete_ty, obj_ty) = obligation.cause.code().peel_derives() &&
                            Some(trait_ref.def_id()) == self.tcx.lang_items().sized_trait() {
                            self.suggest_borrowing_for_object_cast(&mut err, &root_obligation, *concrete_ty, *obj_ty);
                        }

                        let mut unsatisfied_const = false;
                        if trait_predicate.is_const_if_const() && obligation.param_env.is_const() {
                            let non_const_predicate = trait_ref.without_const();
                            let non_const_obligation = Obligation {
                                cause: obligation.cause.clone(),
                                param_env: obligation.param_env.without_const(),
                                predicate: non_const_predicate.to_predicate(tcx),
                                recursion_depth: obligation.recursion_depth,
                            };
                            if self.predicate_may_hold(&non_const_obligation) {
                                unsatisfied_const = true;
                                err.span_note(
                                    span,
                                    &format!(
                                        "the trait `{}` is implemented for `{}`, \
                                        but that implementation is not `const`",
                                        non_const_predicate.print_modifiers_and_trait_path(),
                                        trait_ref.skip_binder().self_ty(),
                                    ),
                                );
                            }
                        }

                        if let Some((msg, span)) = type_def {
                            err.span_label(span, &msg);
                        }
                        if let Some(ref s) = note {
                            // If it has a custom `#[rustc_on_unimplemented]` note, let's display it
                            err.note(s.as_str());
                        }
                        if let Some(ref s) = parent_label {
                            let body = tcx
                                .hir()
                                .opt_local_def_id(obligation.cause.body_id)
                                .unwrap_or_else(|| {
                                    tcx.hir().body_owner_def_id(hir::BodyId {
                                        hir_id: obligation.cause.body_id,
                                    })
                                });
                            err.span_label(tcx.def_span(body), s);
                        }

                        self.suggest_floating_point_literal(&obligation, &mut err, &trait_ref);
                        self.suggest_dereferencing_index(&obligation, &mut err, trait_predicate);
                        let mut suggested =
                            self.suggest_dereferences(&obligation, &mut err, trait_predicate);
                        suggested |= self.suggest_fn_call(&obligation, &mut err, trait_predicate);
                        suggested |=
                            self.suggest_remove_reference(&obligation, &mut err, trait_predicate);
                        suggested |= self.suggest_semicolon_removal(
                            &obligation,
                            &mut err,
                            span,
                            trait_predicate,
                        );
                        self.note_version_mismatch(&mut err, &trait_ref);
                        self.suggest_remove_await(&obligation, &mut err);
                        self.suggest_derive(&obligation, &mut err, trait_predicate);

                        if Some(trait_ref.def_id()) == tcx.lang_items().try_trait() {
                            self.suggest_await_before_try(
                                &mut err,
                                &obligation,
                                trait_predicate,
                                span,
                            );
                        }

                        if self.suggest_impl_trait(&mut err, span, &obligation, trait_predicate) {
                            err.emit();
                            return;
                        }

                        if is_unsize {
                            // If the obligation failed due to a missing implementation of the
                            // `Unsize` trait, give a pointer to why that might be the case
                            err.note(
                                "all implementations of `Unsize` are provided \
                                automatically by the compiler, see \
                                <https://doc.rust-lang.org/stable/std/marker/trait.Unsize.html> \
                                for more information",
                            );
                        }

                        let is_fn_trait = [
                            self.tcx.lang_items().fn_trait(),
                            self.tcx.lang_items().fn_mut_trait(),
                            self.tcx.lang_items().fn_once_trait(),
                        ]
                        .contains(&Some(trait_ref.def_id()));
                        let is_target_feature_fn = if let ty::FnDef(def_id, _) =
                            *trait_ref.skip_binder().self_ty().kind()
                        {
                            !self.tcx.codegen_fn_attrs(def_id).target_features.is_empty()
                        } else {
                            false
                        };
                        if is_fn_trait && is_target_feature_fn {
                            err.note(
                                "`#[target_feature]` functions do not implement the `Fn` traits",
                            );
                        }

                        // Try to report a help message
                        if is_fn_trait
                            && let Ok((implemented_kind, params)) = self.type_implements_fn_trait(
                            obligation.param_env,
                            trait_ref.self_ty(),
                            trait_predicate.skip_binder().constness,
                            trait_predicate.skip_binder().polarity,
                        )
                        {
                            // If the type implements `Fn`, `FnMut`, or `FnOnce`, suppress the following
                            // suggestion to add trait bounds for the type, since we only typically implement
                            // these traits once.

                            // Note if the `FnMut` or `FnOnce` is less general than the trait we're trying
                            // to implement.
                            let selected_kind =
                                ty::ClosureKind::from_def_id(self.tcx, trait_ref.def_id())
                                    .expect("expected to map DefId to ClosureKind");
                            if !implemented_kind.extends(selected_kind) {
                                err.note(
                                    &format!(
                                        "`{}` implements `{}`, but it must implement `{}`, which is more general",
                                        trait_ref.skip_binder().self_ty(),
                                        implemented_kind,
                                        selected_kind
                                    )
                                );
                            }

                            // Note any argument mismatches
                            let given_ty = params.skip_binder();
                            let expected_ty = trait_ref.skip_binder().substs.type_at(1);
                            if let ty::Tuple(given) = given_ty.kind()
                                && let ty::Tuple(expected) = expected_ty.kind()
                            {
                                if expected.len() != given.len() {
                                    // Note number of types that were expected and given
                                    err.note(
                                        &format!(
                                            "expected a closure taking {} argument{}, but one taking {} argument{} was given",
                                            given.len(),
                                            pluralize!(given.len()),
                                            expected.len(),
                                            pluralize!(expected.len()),
                                        )
                                    );
                                } else if !self.same_type_modulo_infer(given_ty, expected_ty) {
                                    // Print type mismatch
                                    let (expected_args, given_args) =
                                        self.cmp(given_ty, expected_ty);
                                    err.note_expected_found(
                                        &"a closure with arguments",
                                        expected_args,
                                        &"a closure with arguments",
                                        given_args,
                                    );
                                }
                            }
                        } else if !trait_ref.has_non_region_infer()
                            && self.predicate_can_apply(obligation.param_env, trait_predicate)
                        {
                            // If a where-clause may be useful, remind the
                            // user that they can add it.
                            //
                            // don't display an on-unimplemented note, as
                            // these notes will often be of the form
                            //     "the type `T` can't be frobnicated"
                            // which is somewhat confusing.
                            self.suggest_restricting_param_bound(
                                &mut err,
                                trait_predicate,
                                None,
                                obligation.cause.body_id,
                            );
                        } else if !suggested && !unsatisfied_const {
                            // Can't show anything else useful, try to find similar impls.
                            let impl_candidates = self.find_similar_impl_candidates(trait_predicate);
                            if !self.report_similar_impl_candidates(
                                impl_candidates,
                                trait_ref,
                                obligation.cause.body_id,
                                &mut err,
                            ) {
                                // This is *almost* equivalent to
                                // `obligation.cause.code().peel_derives()`, but it gives us the
                                // trait predicate for that corresponding root obligation. This
                                // lets us get a derived obligation from a type parameter, like
                                // when calling `string.strip_suffix(p)` where `p` is *not* an
                                // implementer of `Pattern<'_>`.
                                let mut code = obligation.cause.code();
                                let mut trait_pred = trait_predicate;
                                let mut peeled = false;
                                while let Some((parent_code, parent_trait_pred)) = code.parent() {
                                    code = parent_code;
                                    if let Some(parent_trait_pred) = parent_trait_pred {
                                        trait_pred = parent_trait_pred;
                                        peeled = true;
                                    }
                                }
                                let def_id = trait_pred.def_id();
                                // Mention *all* the `impl`s for the *top most* obligation, the
                                // user might have meant to use one of them, if any found. We skip
                                // auto-traits or fundamental traits that might not be exactly what
                                // the user might expect to be presented with. Instead this is
                                // useful for less general traits.
                                if peeled
                                    && !self.tcx.trait_is_auto(def_id)
                                    && !self.tcx.lang_items().items().contains(&Some(def_id))
                                {
                                    let trait_ref = trait_pred.to_poly_trait_ref();
                                    let impl_candidates =
                                        self.find_similar_impl_candidates(trait_pred);
                                    self.report_similar_impl_candidates(
                                        impl_candidates,
                                        trait_ref,
                                        obligation.cause.body_id,
                                        &mut err,
                                    );
                                }
                            }
                        }

                        // Changing mutability doesn't make a difference to whether we have
                        // an `Unsize` impl (Fixes ICE in #71036)
                        if !is_unsize {
                            self.suggest_change_mut(&obligation, &mut err, trait_predicate);
                        }

                        // If this error is due to `!: Trait` not implemented but `(): Trait` is
                        // implemented, and fallback has occurred, then it could be due to a
                        // variable that used to fallback to `()` now falling back to `!`. Issue a
                        // note informing about the change in behaviour.
                        if trait_predicate.skip_binder().self_ty().is_never()
                            && fallback_has_occurred
                        {
                            let predicate = trait_predicate.map_bound(|mut trait_pred| {
                                trait_pred.trait_ref.substs = self.tcx.mk_substs_trait(
                                    self.tcx.mk_unit(),
                                    &trait_pred.trait_ref.substs[1..],
                                );
                                trait_pred
                            });
                            let unit_obligation = obligation.with(predicate.to_predicate(tcx));
                            if self.predicate_may_hold(&unit_obligation) {
                                err.note(
                                    "this error might have been caused by changes to \
                                    Rust's type-inference algorithm (see issue #48950 \
                                    <https://github.com/rust-lang/rust/issues/48950> \
                                    for more information)",
                                );
                                err.help("did you intend to use the type `()` here instead?");
                            }
                        }

                        // Return early if the trait is Debug or Display and the invocation
                        // originates within a standard library macro, because the output
                        // is otherwise overwhelming and unhelpful (see #85844 for an
                        // example).

                        let in_std_macro =
                            match obligation.cause.span.ctxt().outer_expn_data().macro_def_id {
                                Some(macro_def_id) => {
                                    let crate_name = tcx.crate_name(macro_def_id.krate);
                                    crate_name == sym::std || crate_name == sym::core
                                }
                                None => false,
                            };

                        if in_std_macro
                            && matches!(
                                self.tcx.get_diagnostic_name(trait_ref.def_id()),
                                Some(sym::Debug | sym::Display)
                            )
                        {
                            err.emit();
                            return;
                        }

                        err
                    }

                    ty::PredicateKind::Subtype(predicate) => {
                        // Errors for Subtype predicates show up as
                        // `FulfillmentErrorCode::CodeSubtypeError`,
                        // not selection error.
                        span_bug!(span, "subtype requirement gave wrong error: `{:?}`", predicate)
                    }

                    ty::PredicateKind::Coerce(predicate) => {
                        // Errors for Coerce predicates show up as
                        // `FulfillmentErrorCode::CodeSubtypeError`,
                        // not selection error.
                        span_bug!(span, "coerce requirement gave wrong error: `{:?}`", predicate)
                    }

                    ty::PredicateKind::RegionOutlives(..)
                    | ty::PredicateKind::Projection(..)
                    | ty::PredicateKind::TypeOutlives(..) => {
                        let predicate = self.resolve_vars_if_possible(obligation.predicate);
                        struct_span_err!(
                            self.tcx.sess,
                            span,
                            E0280,
                            "the requirement `{}` is not satisfied",
                            predicate
                        )
                    }

                    ty::PredicateKind::ObjectSafe(trait_def_id) => {
                        let violations = self.tcx.object_safety_violations(trait_def_id);
                        report_object_safety_error(self.tcx, span, trait_def_id, violations)
                    }

                    ty::PredicateKind::ClosureKind(closure_def_id, closure_substs, kind) => {
                        let found_kind = self.closure_kind(closure_substs).unwrap();
                        let closure_span = self.tcx.def_span(closure_def_id);
                        let mut err = struct_span_err!(
                            self.tcx.sess,
                            closure_span,
                            E0525,
                            "expected a closure that implements the `{}` trait, \
                             but this closure only implements `{}`",
                            kind,
                            found_kind
                        );

                        err.span_label(
                            closure_span,
                            format!("this closure implements `{}`, not `{}`", found_kind, kind),
                        );
                        err.span_label(
                            obligation.cause.span,
                            format!("the requirement to implement `{}` derives from here", kind),
                        );

                        // Additional context information explaining why the closure only implements
                        // a particular trait.
                        if let Some(typeck_results) = &self.typeck_results {
                            let hir_id = self
                                .tcx
                                .hir()
                                .local_def_id_to_hir_id(closure_def_id.expect_local());
                            match (found_kind, typeck_results.closure_kind_origins().get(hir_id)) {
                                (ty::ClosureKind::FnOnce, Some((span, place))) => {
                                    err.span_label(
                                        *span,
                                        format!(
                                            "closure is `FnOnce` because it moves the \
                                         variable `{}` out of its environment",
                                            ty::place_to_string_for_capture(tcx, place)
                                        ),
                                    );
                                }
                                (ty::ClosureKind::FnMut, Some((span, place))) => {
                                    err.span_label(
                                        *span,
                                        format!(
                                            "closure is `FnMut` because it mutates the \
                                         variable `{}` here",
                                            ty::place_to_string_for_capture(tcx, place)
                                        ),
                                    );
                                }
                                _ => {}
                            }
                        }

                        err
                    }

                    ty::PredicateKind::WellFormed(ty) => {
                        if !self.tcx.sess.opts.unstable_opts.chalk {
                            // WF predicates cannot themselves make
                            // errors. They can only block due to
                            // ambiguity; otherwise, they always
                            // degenerate into other obligations
                            // (which may fail).
                            span_bug!(span, "WF predicate not satisfied for {:?}", ty);
                        } else {
                            // FIXME: we'll need a better message which takes into account
                            // which bounds actually failed to hold.
                            self.tcx.sess.struct_span_err(
                                span,
                                &format!("the type `{}` is not well-formed (chalk)", ty),
                            )
                        }
                    }

                    ty::PredicateKind::ConstEvaluatable(..) => {
                        // Errors for `ConstEvaluatable` predicates show up as
                        // `SelectionError::ConstEvalFailure`,
                        // not `Unimplemented`.
                        span_bug!(
                            span,
                            "const-evaluatable requirement gave wrong error: `{:?}`",
                            obligation
                        )
                    }

                    ty::PredicateKind::ConstEquate(..) => {
                        // Errors for `ConstEquate` predicates show up as
                        // `SelectionError::ConstEvalFailure`,
                        // not `Unimplemented`.
                        span_bug!(
                            span,
                            "const-equate requirement gave wrong error: `{:?}`",
                            obligation
                        )
                    }

                    ty::PredicateKind::TypeWellFormedFromEnv(..) => span_bug!(
                        span,
                        "TypeWellFormedFromEnv predicate should only exist in the environment"
                    ),
                }
            }

            OutputTypeParameterMismatch(found_trait_ref, expected_trait_ref, _) => {
                let found_trait_ref = self.resolve_vars_if_possible(found_trait_ref);
                let expected_trait_ref = self.resolve_vars_if_possible(expected_trait_ref);

                if expected_trait_ref.self_ty().references_error() {
                    return;
                }

                let Some(found_trait_ty) = found_trait_ref.self_ty().no_bound_vars() else {
                    return;
                };

                let found_did = match *found_trait_ty.kind() {
                    ty::Closure(did, _)
                    | ty::Foreign(did)
                    | ty::FnDef(did, _)
                    | ty::Generator(did, ..) => Some(did),
                    ty::Adt(def, _) => Some(def.did()),
                    _ => None,
                };

                let found_span = found_did.and_then(|did| self.tcx.hir().span_if_local(did));

                if self.reported_closure_mismatch.borrow().contains(&(span, found_span)) {
                    // We check closures twice, with obligations flowing in different directions,
                    // but we want to complain about them only once.
                    return;
                }

                self.reported_closure_mismatch.borrow_mut().insert((span, found_span));

                let mut not_tupled = false;

                let found = match found_trait_ref.skip_binder().substs.type_at(1).kind() {
                    ty::Tuple(ref tys) => vec![ArgKind::empty(); tys.len()],
                    _ => {
                        not_tupled = true;
                        vec![ArgKind::empty()]
                    }
                };

                let expected_ty = expected_trait_ref.skip_binder().substs.type_at(1);
                let expected = match expected_ty.kind() {
                    ty::Tuple(ref tys) => {
                        tys.iter().map(|t| ArgKind::from_expected_ty(t, Some(span))).collect()
                    }
                    _ => {
                        not_tupled = true;
                        vec![ArgKind::Arg("_".to_owned(), expected_ty.to_string())]
                    }
                };

                // If this is a `Fn` family trait and either the expected or found
                // is not tupled, then fall back to just a regular mismatch error.
                // This shouldn't be common unless manually implementing one of the
                // traits manually, but don't make it more confusing when it does
                // happen.
                if Some(expected_trait_ref.def_id()) != tcx.lang_items().gen_trait() && not_tupled {
                    self.report_and_explain_type_error(
                        TypeTrace::poly_trait_refs(
                            &obligation.cause,
                            true,
                            expected_trait_ref,
                            found_trait_ref,
                        ),
                        ty::error::TypeError::Mismatch,
                    )
                } else if found.len() == expected.len() {
                    self.report_closure_arg_mismatch(
                        span,
                        found_span,
                        found_trait_ref,
                        expected_trait_ref,
                        obligation.cause.code(),
                    )
                } else {
                    let (closure_span, found) = found_did
                        .and_then(|did| {
                            let node = self.tcx.hir().get_if_local(did)?;
                            let (found_span, found) = self.get_fn_like_arguments(node)?;
                            Some((Some(found_span), found))
                        })
                        .unwrap_or((found_span, found));

                    self.report_arg_count_mismatch(
                        span,
                        closure_span,
                        expected,
                        found,
                        found_trait_ty.is_closure(),
                    )
                }
            }

            TraitNotObjectSafe(did) => {
                let violations = self.tcx.object_safety_violations(did);
                report_object_safety_error(self.tcx, span, did, violations)
            }

            SelectionError::NotConstEvaluatable(NotConstEvaluatable::MentionsInfer) => {
                bug!(
                    "MentionsInfer should have been handled in `traits/fulfill.rs` or `traits/select/mod.rs`"
                )
            }
            SelectionError::NotConstEvaluatable(NotConstEvaluatable::MentionsParam) => {
                if !self.tcx.features().generic_const_exprs {
                    let mut err = self.tcx.sess.struct_span_err(
                        span,
                        "constant expression depends on a generic parameter",
                    );
                    // FIXME(const_generics): we should suggest to the user how they can resolve this
                    // issue. However, this is currently not actually possible
                    // (see https://github.com/rust-lang/rust/issues/66962#issuecomment-575907083).
                    //
                    // Note that with `feature(generic_const_exprs)` this case should not
                    // be reachable.
                    err.note("this may fail depending on what value the parameter takes");
                    err.emit();
                    return;
                }

                match obligation.predicate.kind().skip_binder() {
                    ty::PredicateKind::ConstEvaluatable(ct) => {
                        let ty::ConstKind::Unevaluated(uv) = ct.kind() else {
                            bug!("const evaluatable failed for non-unevaluated const `{ct:?}`");
                        };
                        let mut err =
                            self.tcx.sess.struct_span_err(span, "unconstrained generic constant");
                        let const_span = self.tcx.def_span(uv.def.did);
                        match self.tcx.sess.source_map().span_to_snippet(const_span) {
                            Ok(snippet) => err.help(&format!(
                                "try adding a `where` bound using this expression: `where [(); {}]:`",
                                snippet
                            )),
                            _ => err.help("consider adding a `where` bound using this expression"),
                        };
                        err
                    }
                    _ => {
                        span_bug!(
                            span,
                            "unexpected non-ConstEvaluatable predicate, this should not be reachable"
                        )
                    }
                }
            }

            // Already reported in the query.
            SelectionError::NotConstEvaluatable(NotConstEvaluatable::Error(_)) => {
                // FIXME(eddyb) remove this once `ErrorGuaranteed` becomes a proof token.
                self.tcx.sess.delay_span_bug(span, "`ErrorGuaranteed` without an error");
                return;
            }
            // Already reported.
            Overflow(OverflowError::Error(_)) => {
                self.tcx.sess.delay_span_bug(span, "`OverflowError` has been reported");
                return;
            }
            Overflow(_) => {
                bug!("overflow should be handled before the `report_selection_error` path");
            }
            SelectionError::ErrorReporting => {
                bug!("ErrorReporting Overflow should not reach `report_selection_err` call")
            }
        };

        self.note_obligation_cause(&mut err, &obligation);
        self.point_at_returns_when_relevant(&mut err, &obligation);

        err.emit();
    }
}

trait InferCtxtPrivExt<'tcx> {
    // returns if `cond` not occurring implies that `error` does not occur - i.e., that
    // `error` occurring implies that `cond` occurs.
    fn error_implies(&self, cond: ty::Predicate<'tcx>, error: ty::Predicate<'tcx>) -> bool;

    fn report_fulfillment_error(
        &self,
        error: &FulfillmentError<'tcx>,
        body_id: Option<hir::BodyId>,
        fallback_has_occurred: bool,
    );

    fn report_projection_error(
        &self,
        obligation: &PredicateObligation<'tcx>,
        error: &MismatchedProjectionTypes<'tcx>,
    );

    fn maybe_detailed_projection_msg(
        &self,
        pred: ty::ProjectionPredicate<'tcx>,
        normalized_ty: ty::Term<'tcx>,
        expected_ty: ty::Term<'tcx>,
    ) -> Option<String>;

    fn fuzzy_match_tys(
        &self,
        a: Ty<'tcx>,
        b: Ty<'tcx>,
        ignoring_lifetimes: bool,
    ) -> Option<CandidateSimilarity>;

    fn describe_generator(&self, body_id: hir::BodyId) -> Option<&'static str>;

    fn find_similar_impl_candidates(
        &self,
        trait_pred: ty::PolyTraitPredicate<'tcx>,
    ) -> Vec<ImplCandidate<'tcx>>;

    fn report_similar_impl_candidates(
        &self,
        impl_candidates: Vec<ImplCandidate<'tcx>>,
        trait_ref: ty::PolyTraitRef<'tcx>,
        body_id: hir::HirId,
        err: &mut Diagnostic,
    ) -> bool;

    /// Gets the parent trait chain start
    fn get_parent_trait_ref(
        &self,
        code: &ObligationCauseCode<'tcx>,
    ) -> Option<(String, Option<Span>)>;

    /// If the `Self` type of the unsatisfied trait `trait_ref` implements a trait
    /// with the same path as `trait_ref`, a help message about
    /// a probable version mismatch is added to `err`
    fn note_version_mismatch(
        &self,
        err: &mut Diagnostic,
        trait_ref: &ty::PolyTraitRef<'tcx>,
    ) -> bool;

    /// Creates a `PredicateObligation` with `new_self_ty` replacing the existing type in the
    /// `trait_ref`.
    ///
    /// For this to work, `new_self_ty` must have no escaping bound variables.
    fn mk_trait_obligation_with_new_self_ty(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        trait_ref_and_ty: ty::Binder<'tcx, (ty::TraitPredicate<'tcx>, Ty<'tcx>)>,
    ) -> PredicateObligation<'tcx>;

    fn maybe_report_ambiguity(
        &self,
        obligation: &PredicateObligation<'tcx>,
        body_id: Option<hir::BodyId>,
    );

    fn predicate_can_apply(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        pred: ty::PolyTraitPredicate<'tcx>,
    ) -> bool;

    fn note_obligation_cause(&self, err: &mut Diagnostic, obligation: &PredicateObligation<'tcx>);

    fn suggest_unsized_bound_if_applicable(
        &self,
        err: &mut Diagnostic,
        obligation: &PredicateObligation<'tcx>,
    );

    fn annotate_source_of_ambiguity(
        &self,
        err: &mut Diagnostic,
        impls: &[DefId],
        predicate: ty::Predicate<'tcx>,
    );

    fn maybe_suggest_unsized_generics(&self, err: &mut Diagnostic, span: Span, node: Node<'tcx>);

    fn maybe_indirection_for_unsized(
        &self,
        err: &mut Diagnostic,
        item: &'tcx Item<'tcx>,
        param: &'tcx GenericParam<'tcx>,
    ) -> bool;

    fn is_recursive_obligation(
        &self,
        obligated_types: &mut Vec<Ty<'tcx>>,
        cause_code: &ObligationCauseCode<'tcx>,
    ) -> bool;
}

impl<'tcx> InferCtxtPrivExt<'tcx> for TypeErrCtxt<'_, 'tcx> {
    // returns if `cond` not occurring implies that `error` does not occur - i.e., that
    // `error` occurring implies that `cond` occurs.
    fn error_implies(&self, cond: ty::Predicate<'tcx>, error: ty::Predicate<'tcx>) -> bool {
        if cond == error {
            return true;
        }

        // FIXME: It should be possible to deal with `ForAll` in a cleaner way.
        let bound_error = error.kind();
        let (cond, error) = match (cond.kind().skip_binder(), bound_error.skip_binder()) {
            (ty::PredicateKind::Trait(..), ty::PredicateKind::Trait(error)) => {
                (cond, bound_error.rebind(error))
            }
            _ => {
                // FIXME: make this work in other cases too.
                return false;
            }
        };

        for obligation in super::elaborate_predicates(self.tcx, std::iter::once(cond)) {
            let bound_predicate = obligation.predicate.kind();
            if let ty::PredicateKind::Trait(implication) = bound_predicate.skip_binder() {
                let error = error.to_poly_trait_ref();
                let implication = bound_predicate.rebind(implication.trait_ref);
                // FIXME: I'm just not taking associated types at all here.
                // Eventually I'll need to implement param-env-aware
                // `Γ₁ ⊦ φ₁ => Γ₂ ⊦ φ₂` logic.
                let param_env = ty::ParamEnv::empty();
                if self.can_sub(param_env, error, implication).is_ok() {
                    debug!("error_implies: {:?} -> {:?} -> {:?}", cond, error, implication);
                    return true;
                }
            }
        }

        false
    }

    #[instrument(skip(self), level = "debug")]
    fn report_fulfillment_error(
        &self,
        error: &FulfillmentError<'tcx>,
        body_id: Option<hir::BodyId>,
        fallback_has_occurred: bool,
    ) {
        match error.code {
            FulfillmentErrorCode::CodeSelectionError(ref selection_error) => {
                self.report_selection_error(
                    error.obligation.clone(),
                    &error.root_obligation,
                    selection_error,
                    fallback_has_occurred,
                );
            }
            FulfillmentErrorCode::CodeProjectionError(ref e) => {
                self.report_projection_error(&error.obligation, e);
            }
            FulfillmentErrorCode::CodeAmbiguity => {
                self.maybe_report_ambiguity(&error.obligation, body_id);
            }
            FulfillmentErrorCode::CodeSubtypeError(ref expected_found, ref err) => {
                self.report_mismatched_types(
                    &error.obligation.cause,
                    expected_found.expected,
                    expected_found.found,
                    err.clone(),
                )
                .emit();
            }
            FulfillmentErrorCode::CodeConstEquateError(ref expected_found, ref err) => {
                let mut diag = self.report_mismatched_consts(
                    &error.obligation.cause,
                    expected_found.expected,
                    expected_found.found,
                    err.clone(),
                );
                let code = error.obligation.cause.code().peel_derives().peel_match_impls();
                if let ObligationCauseCode::BindingObligation(..)
                | ObligationCauseCode::ItemObligation(..)
                | ObligationCauseCode::ExprBindingObligation(..)
                | ObligationCauseCode::ExprItemObligation(..) = code
                {
                    self.note_obligation_cause_code(
                        &mut diag,
                        &error.obligation.predicate,
                        error.obligation.param_env,
                        code,
                        &mut vec![],
                        &mut Default::default(),
                    );
                }
                diag.emit();
            }
            FulfillmentErrorCode::CodeCycle(ref cycle) => {
                self.report_overflow_error_cycle(cycle);
            }
        }
    }

    #[instrument(level = "debug", skip_all)]
    fn report_projection_error(
        &self,
        obligation: &PredicateObligation<'tcx>,
        error: &MismatchedProjectionTypes<'tcx>,
    ) {
        let predicate = self.resolve_vars_if_possible(obligation.predicate);

        if predicate.references_error() {
            return;
        }

        self.probe(|_| {
            let mut err = error.err;
            let mut values = None;

            // try to find the mismatched types to report the error with.
            //
            // this can fail if the problem was higher-ranked, in which
            // cause I have no idea for a good error message.
            let bound_predicate = predicate.kind();
            if let ty::PredicateKind::Projection(data) = bound_predicate.skip_binder() {
                let mut selcx = SelectionContext::new(self);
                let data = self.replace_bound_vars_with_fresh_vars(
                    obligation.cause.span,
                    infer::LateBoundRegionConversionTime::HigherRankedType,
                    bound_predicate.rebind(data),
                );
                let mut obligations = vec![];
                let normalized_ty = super::normalize_projection_type(
                    &mut selcx,
                    obligation.param_env,
                    data.projection_ty,
                    obligation.cause.clone(),
                    0,
                    &mut obligations,
                );

                debug!(?obligation.cause, ?obligation.param_env);

                debug!(?normalized_ty, data.ty = ?data.term);

                let is_normalized_ty_expected = !matches!(
                    obligation.cause.code().peel_derives(),
                    ObligationCauseCode::ItemObligation(_)
                        | ObligationCauseCode::BindingObligation(_, _)
                        | ObligationCauseCode::ExprItemObligation(..)
                        | ObligationCauseCode::ExprBindingObligation(..)
                        | ObligationCauseCode::ObjectCastObligation(..)
                        | ObligationCauseCode::OpaqueType
                );
                if let Err(new_err) = self.at(&obligation.cause, obligation.param_env).eq_exp(
                    is_normalized_ty_expected,
                    normalized_ty,
                    data.term,
                ) {
                    values = Some((data, is_normalized_ty_expected, normalized_ty, data.term));
                    err = new_err;
                }
            }

            let msg = values
                .and_then(|(predicate, _, normalized_ty, expected_ty)| {
                    self.maybe_detailed_projection_msg(predicate, normalized_ty, expected_ty)
                })
                .unwrap_or_else(|| format!("type mismatch resolving `{}`", predicate));
            let mut diag = struct_span_err!(self.tcx.sess, obligation.cause.span, E0271, "{msg}");

            let secondary_span = match predicate.kind().skip_binder() {
                ty::PredicateKind::Projection(proj) => self
                    .tcx
                    .opt_associated_item(proj.projection_ty.item_def_id)
                    .and_then(|trait_assoc_item| {
                        self.tcx
                            .trait_of_item(proj.projection_ty.item_def_id)
                            .map(|id| (trait_assoc_item, id))
                    })
                    .and_then(|(trait_assoc_item, id)| {
                        let trait_assoc_ident = trait_assoc_item.ident(self.tcx);
                        self.tcx.find_map_relevant_impl(id, proj.projection_ty.self_ty(), |did| {
                            self.tcx
                                .associated_items(did)
                                .in_definition_order()
                                .find(|assoc| assoc.ident(self.tcx) == trait_assoc_ident)
                        })
                    })
                    .and_then(|item| match self.tcx.hir().get_if_local(item.def_id) {
                        Some(
                            hir::Node::TraitItem(hir::TraitItem {
                                kind: hir::TraitItemKind::Type(_, Some(ty)),
                                ..
                            })
                            | hir::Node::ImplItem(hir::ImplItem {
                                kind: hir::ImplItemKind::Type(ty),
                                ..
                            }),
                        ) => Some((ty.span, format!("type mismatch resolving `{}`", predicate))),
                        _ => None,
                    }),
                _ => None,
            };
            self.note_type_err(
                &mut diag,
                &obligation.cause,
                secondary_span,
                values.map(|(_, is_normalized_ty_expected, normalized_ty, term)| {
                    infer::ValuePairs::Terms(ExpectedFound::new(
                        is_normalized_ty_expected,
                        normalized_ty,
                        term,
                    ))
                }),
                err,
                true,
                false,
            );
            self.note_obligation_cause(&mut diag, obligation);
            diag.emit();
        });
    }

    fn maybe_detailed_projection_msg(
        &self,
        pred: ty::ProjectionPredicate<'tcx>,
        normalized_ty: ty::Term<'tcx>,
        expected_ty: ty::Term<'tcx>,
    ) -> Option<String> {
        let trait_def_id = pred.projection_ty.trait_def_id(self.tcx);
        let self_ty = pred.projection_ty.self_ty();

        if Some(pred.projection_ty.item_def_id) == self.tcx.lang_items().fn_once_output() {
            Some(format!(
                "expected `{self_ty}` to be a {fn_kind} that returns `{expected_ty}`, but it returns `{normalized_ty}`",
                fn_kind = self_ty.prefix_string(self.tcx)
            ))
        } else if Some(trait_def_id) == self.tcx.lang_items().future_trait() {
            Some(format!(
                "expected `{self_ty}` to be a future that resolves to `{expected_ty}`, but it resolves to `{normalized_ty}`"
            ))
        } else if Some(trait_def_id) == self.tcx.get_diagnostic_item(sym::Iterator) {
            Some(format!(
                "expected `{self_ty}` to be an iterator that yields `{expected_ty}`, but it yields `{normalized_ty}`"
            ))
        } else {
            None
        }
    }

    fn fuzzy_match_tys(
        &self,
        mut a: Ty<'tcx>,
        mut b: Ty<'tcx>,
        ignoring_lifetimes: bool,
    ) -> Option<CandidateSimilarity> {
        /// returns the fuzzy category of a given type, or None
        /// if the type can be equated to any type.
        fn type_category(tcx: TyCtxt<'_>, t: Ty<'_>) -> Option<u32> {
            match t.kind() {
                ty::Bool => Some(0),
                ty::Char => Some(1),
                ty::Str => Some(2),
                ty::Adt(def, _) if tcx.is_diagnostic_item(sym::String, def.did()) => Some(2),
                ty::Int(..)
                | ty::Uint(..)
                | ty::Float(..)
                | ty::Infer(ty::IntVar(..) | ty::FloatVar(..)) => Some(4),
                ty::Ref(..) | ty::RawPtr(..) => Some(5),
                ty::Array(..) | ty::Slice(..) => Some(6),
                ty::FnDef(..) | ty::FnPtr(..) => Some(7),
                ty::Dynamic(..) => Some(8),
                ty::Closure(..) => Some(9),
                ty::Tuple(..) => Some(10),
                ty::Param(..) => Some(11),
                ty::Projection(..) => Some(12),
                ty::Opaque(..) => Some(13),
                ty::Never => Some(14),
                ty::Adt(..) => Some(15),
                ty::Generator(..) => Some(16),
                ty::Foreign(..) => Some(17),
                ty::GeneratorWitness(..) => Some(18),
                ty::Placeholder(..) | ty::Bound(..) | ty::Infer(..) | ty::Error(_) => None,
            }
        }

        let strip_references = |mut t: Ty<'tcx>| -> Ty<'tcx> {
            loop {
                match t.kind() {
                    ty::Ref(_, inner, _) | ty::RawPtr(ty::TypeAndMut { ty: inner, .. }) => {
                        t = *inner
                    }
                    _ => break t,
                }
            }
        };

        if !ignoring_lifetimes {
            a = strip_references(a);
            b = strip_references(b);
        }

        let cat_a = type_category(self.tcx, a)?;
        let cat_b = type_category(self.tcx, b)?;
        if a == b {
            Some(CandidateSimilarity::Exact { ignoring_lifetimes })
        } else if cat_a == cat_b {
            match (a.kind(), b.kind()) {
                (ty::Adt(def_a, _), ty::Adt(def_b, _)) => def_a == def_b,
                (ty::Foreign(def_a), ty::Foreign(def_b)) => def_a == def_b,
                // Matching on references results in a lot of unhelpful
                // suggestions, so let's just not do that for now.
                //
                // We still upgrade successful matches to `ignoring_lifetimes: true`
                // to prioritize that impl.
                (ty::Ref(..) | ty::RawPtr(..), ty::Ref(..) | ty::RawPtr(..)) => {
                    self.fuzzy_match_tys(a, b, true).is_some()
                }
                _ => true,
            }
            .then_some(CandidateSimilarity::Fuzzy { ignoring_lifetimes })
        } else if ignoring_lifetimes {
            None
        } else {
            self.fuzzy_match_tys(a, b, true)
        }
    }

    fn describe_generator(&self, body_id: hir::BodyId) -> Option<&'static str> {
        self.tcx.hir().body(body_id).generator_kind.map(|gen_kind| match gen_kind {
            hir::GeneratorKind::Gen => "a generator",
            hir::GeneratorKind::Async(hir::AsyncGeneratorKind::Block) => "an async block",
            hir::GeneratorKind::Async(hir::AsyncGeneratorKind::Fn) => "an async function",
            hir::GeneratorKind::Async(hir::AsyncGeneratorKind::Closure) => "an async closure",
        })
    }

    fn find_similar_impl_candidates(
        &self,
        trait_pred: ty::PolyTraitPredicate<'tcx>,
    ) -> Vec<ImplCandidate<'tcx>> {
        self.tcx
            .all_impls(trait_pred.def_id())
            .filter_map(|def_id| {
                if self.tcx.impl_polarity(def_id) == ty::ImplPolarity::Negative
                    || !trait_pred
                        .skip_binder()
                        .is_constness_satisfied_by(self.tcx.constness(def_id))
                {
                    return None;
                }

                let imp = self.tcx.impl_trait_ref(def_id).unwrap();

                self.fuzzy_match_tys(trait_pred.skip_binder().self_ty(), imp.self_ty(), false)
                    .map(|similarity| ImplCandidate { trait_ref: imp, similarity })
            })
            .collect()
    }

    fn report_similar_impl_candidates(
        &self,
        impl_candidates: Vec<ImplCandidate<'tcx>>,
        trait_ref: ty::PolyTraitRef<'tcx>,
        body_id: hir::HirId,
        err: &mut Diagnostic,
    ) -> bool {
        let report = |mut candidates: Vec<TraitRef<'tcx>>, err: &mut Diagnostic| {
            candidates.sort();
            candidates.dedup();
            let len = candidates.len();
            if candidates.len() == 0 {
                return false;
            }
            if candidates.len() == 1 {
                let ty_desc = match candidates[0].self_ty().kind() {
                    ty::FnPtr(_) => Some("fn pointer"),
                    _ => None,
                };
                let the_desc = match ty_desc {
                    Some(desc) => format!(" implemented for {} `", desc),
                    None => " implemented for `".to_string(),
                };
                err.highlighted_help(vec![
                    (
                        format!("the trait `{}` ", candidates[0].print_only_trait_path()),
                        Style::NoStyle,
                    ),
                    ("is".to_string(), Style::Highlight),
                    (the_desc, Style::NoStyle),
                    (candidates[0].self_ty().to_string(), Style::Highlight),
                    ("`".to_string(), Style::NoStyle),
                ]);
                return true;
            }
            let trait_ref = TraitRef::identity(self.tcx, candidates[0].def_id);
            // Check if the trait is the same in all cases. If so, we'll only show the type.
            let mut traits: Vec<_> =
                candidates.iter().map(|c| c.print_only_trait_path().to_string()).collect();
            traits.sort();
            traits.dedup();

            let mut candidates: Vec<String> = candidates
                .into_iter()
                .map(|c| {
                    if traits.len() == 1 {
                        format!("\n  {}", c.self_ty())
                    } else {
                        format!("\n  {}", c)
                    }
                })
                .collect();

            candidates.sort();
            candidates.dedup();
            let end = if candidates.len() <= 9 { candidates.len() } else { 8 };
            err.help(&format!(
                "the following other types implement trait `{}`:{}{}",
                trait_ref.print_only_trait_path(),
                candidates[..end].join(""),
                if len > 9 { format!("\nand {} others", len - 8) } else { String::new() }
            ));
            true
        };

        let def_id = trait_ref.def_id();
        if impl_candidates.is_empty() {
            if self.tcx.trait_is_auto(def_id)
                || self.tcx.lang_items().items().contains(&Some(def_id))
                || self.tcx.get_diagnostic_name(def_id).is_some()
            {
                // Mentioning implementers of `Copy`, `Debug` and friends is not useful.
                return false;
            }
            let normalized_impl_candidates: Vec<_> = self
                .tcx
                .all_impls(def_id)
                // Ignore automatically derived impls and `!Trait` impls.
                .filter(|&def_id| {
                    self.tcx.impl_polarity(def_id) != ty::ImplPolarity::Negative
                        || self.tcx.is_builtin_derive(def_id)
                })
                .filter_map(|def_id| self.tcx.impl_trait_ref(def_id))
                .filter(|trait_ref| {
                    let self_ty = trait_ref.self_ty();
                    // Avoid mentioning type parameters.
                    if let ty::Param(_) = self_ty.kind() {
                        false
                    }
                    // Avoid mentioning types that are private to another crate
                    else if let ty::Adt(def, _) = self_ty.peel_refs().kind() {
                        // FIXME(compiler-errors): This could be generalized, both to
                        // be more granular, and probably look past other `#[fundamental]`
                        // types, too.
                        self.tcx
                            .visibility(def.did())
                            .is_accessible_from(body_id.owner.def_id, self.tcx)
                    } else {
                        true
                    }
                })
                .collect();
            return report(normalized_impl_candidates, err);
        }

        let normalize = |candidate| {
            let infcx = self.tcx.infer_ctxt().build();
            infcx
                .at(&ObligationCause::dummy(), ty::ParamEnv::empty())
                .normalize(candidate)
                .map_or(candidate, |normalized| normalized.value)
        };

        // Sort impl candidates so that ordering is consistent for UI tests.
        // because the ordering of `impl_candidates` may not be deterministic:
        // https://github.com/rust-lang/rust/pull/57475#issuecomment-455519507
        //
        // Prefer more similar candidates first, then sort lexicographically
        // by their normalized string representation.
        let mut normalized_impl_candidates_and_similarities = impl_candidates
            .into_iter()
            .map(|ImplCandidate { trait_ref, similarity }| {
                let normalized = normalize(trait_ref);
                (similarity, normalized)
            })
            .collect::<Vec<_>>();
        normalized_impl_candidates_and_similarities.sort();
        normalized_impl_candidates_and_similarities.dedup();

        let normalized_impl_candidates = normalized_impl_candidates_and_similarities
            .into_iter()
            .map(|(_, normalized)| normalized)
            .collect::<Vec<_>>();

        report(normalized_impl_candidates, err)
    }

    /// Gets the parent trait chain start
    fn get_parent_trait_ref(
        &self,
        code: &ObligationCauseCode<'tcx>,
    ) -> Option<(String, Option<Span>)> {
        match code {
            ObligationCauseCode::BuiltinDerivedObligation(data) => {
                let parent_trait_ref = self.resolve_vars_if_possible(data.parent_trait_pred);
                match self.get_parent_trait_ref(&data.parent_code) {
                    Some(t) => Some(t),
                    None => {
                        let ty = parent_trait_ref.skip_binder().self_ty();
                        let span = TyCategory::from_ty(self.tcx, ty)
                            .map(|(_, def_id)| self.tcx.def_span(def_id));
                        Some((ty.to_string(), span))
                    }
                }
            }
            ObligationCauseCode::FunctionArgumentObligation { parent_code, .. } => {
                self.get_parent_trait_ref(&parent_code)
            }
            _ => None,
        }
    }

    /// If the `Self` type of the unsatisfied trait `trait_ref` implements a trait
    /// with the same path as `trait_ref`, a help message about
    /// a probable version mismatch is added to `err`
    fn note_version_mismatch(
        &self,
        err: &mut Diagnostic,
        trait_ref: &ty::PolyTraitRef<'tcx>,
    ) -> bool {
        let get_trait_impl = |trait_def_id| {
            self.tcx.find_map_relevant_impl(trait_def_id, trait_ref.skip_binder().self_ty(), Some)
        };
        let required_trait_path = self.tcx.def_path_str(trait_ref.def_id());
        let traits_with_same_path: std::collections::BTreeSet<_> = self
            .tcx
            .all_traits()
            .filter(|trait_def_id| *trait_def_id != trait_ref.def_id())
            .filter(|trait_def_id| self.tcx.def_path_str(*trait_def_id) == required_trait_path)
            .collect();
        let mut suggested = false;
        for trait_with_same_path in traits_with_same_path {
            if let Some(impl_def_id) = get_trait_impl(trait_with_same_path) {
                let impl_span = self.tcx.def_span(impl_def_id);
                err.span_help(impl_span, "trait impl with same name found");
                let trait_crate = self.tcx.crate_name(trait_with_same_path.krate);
                let crate_msg = format!(
                    "perhaps two different versions of crate `{}` are being used?",
                    trait_crate
                );
                err.note(&crate_msg);
                suggested = true;
            }
        }
        suggested
    }

    fn mk_trait_obligation_with_new_self_ty(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        trait_ref_and_ty: ty::Binder<'tcx, (ty::TraitPredicate<'tcx>, Ty<'tcx>)>,
    ) -> PredicateObligation<'tcx> {
        let trait_pred = trait_ref_and_ty.map_bound_ref(|(tr, new_self_ty)| ty::TraitPredicate {
            trait_ref: ty::TraitRef {
                substs: self.tcx.mk_substs_trait(*new_self_ty, &tr.trait_ref.substs[1..]),
                ..tr.trait_ref
            },
            ..*tr
        });

        Obligation::new(ObligationCause::dummy(), param_env, trait_pred.to_predicate(self.tcx))
    }

    #[instrument(skip(self), level = "debug")]
    fn maybe_report_ambiguity(
        &self,
        obligation: &PredicateObligation<'tcx>,
        body_id: Option<hir::BodyId>,
    ) {
        // Unable to successfully determine, probably means
        // insufficient type information, but could mean
        // ambiguous impls. The latter *ought* to be a
        // coherence violation, so we don't report it here.

        let predicate = self.resolve_vars_if_possible(obligation.predicate);
        let span = obligation.cause.span;

        debug!(?predicate, obligation.cause.code = ?obligation.cause.code());

        // Ambiguity errors are often caused as fallout from earlier errors.
        // We ignore them if this `infcx` is tainted in some cases below.

        let bound_predicate = predicate.kind();
        let mut err = match bound_predicate.skip_binder() {
            ty::PredicateKind::Trait(data) => {
                let trait_ref = bound_predicate.rebind(data.trait_ref);
                debug!(?trait_ref);

                if predicate.references_error() {
                    return;
                }

                // This is kind of a hack: it frequently happens that some earlier
                // error prevents types from being fully inferred, and then we get
                // a bunch of uninteresting errors saying something like "<generic
                // #0> doesn't implement Sized".  It may even be true that we
                // could just skip over all checks where the self-ty is an
                // inference variable, but I was afraid that there might be an
                // inference variable created, registered as an obligation, and
                // then never forced by writeback, and hence by skipping here we'd
                // be ignoring the fact that we don't KNOW the type works
                // out. Though even that would probably be harmless, given that
                // we're only talking about builtin traits, which are known to be
                // inhabited. We used to check for `self.tcx.sess.has_errors()` to
                // avoid inundating the user with unnecessary errors, but we now
                // check upstream for type errors and don't add the obligations to
                // begin with in those cases.
                if self.tcx.lang_items().sized_trait() == Some(trait_ref.def_id()) {
                    if !self.is_tainted_by_errors() {
                        self.emit_inference_failure_err(
                            body_id,
                            span,
                            trait_ref.self_ty().skip_binder().into(),
                            ErrorCode::E0282,
                            false,
                        )
                        .emit();
                    }
                    return;
                }

                // Typically, this ambiguity should only happen if
                // there are unresolved type inference variables
                // (otherwise it would suggest a coherence
                // failure). But given #21974 that is not necessarily
                // the case -- we can have multiple where clauses that
                // are only distinguished by a region, which results
                // in an ambiguity even when all types are fully
                // known, since we don't dispatch based on region
                // relationships.

                // Pick the first substitution that still contains inference variables as the one
                // we're going to emit an error for. If there are none (see above), fall back to
                // a more general error.
                let subst = data.trait_ref.substs.iter().find(|s| s.has_non_region_infer());

                let mut err = if let Some(subst) = subst {
                    self.emit_inference_failure_err(body_id, span, subst, ErrorCode::E0283, true)
                } else {
                    struct_span_err!(
                        self.tcx.sess,
                        span,
                        E0283,
                        "type annotations needed: cannot satisfy `{}`",
                        predicate,
                    )
                };

                let obligation = Obligation::new(
                    obligation.cause.clone(),
                    obligation.param_env,
                    trait_ref.to_poly_trait_predicate(),
                );
                let mut selcx = SelectionContext::with_query_mode(
                    &self,
                    crate::traits::TraitQueryMode::Standard,
                );
                match selcx.select_from_obligation(&obligation) {
                    Err(SelectionError::Ambiguous(impls)) if impls.len() > 1 => {
                        self.annotate_source_of_ambiguity(&mut err, &impls, predicate);
                    }
                    _ => {
                        if self.is_tainted_by_errors() {
                            err.cancel();
                            return;
                        }
                        err.note(&format!("cannot satisfy `{}`", predicate));
                    }
                }

                if let ObligationCauseCode::ItemObligation(def_id) | ObligationCauseCode::ExprItemObligation(def_id, ..) = *obligation.cause.code() {
                    self.suggest_fully_qualified_path(&mut err, def_id, span, trait_ref.def_id());
                } else if let Ok(snippet) = &self.tcx.sess.source_map().span_to_snippet(span)
                    && let ObligationCauseCode::BindingObligation(def_id, _) | ObligationCauseCode::ExprBindingObligation(def_id, ..)
                        = *obligation.cause.code()
                {
                    let generics = self.tcx.generics_of(def_id);
                    if generics.params.iter().any(|p| p.name != kw::SelfUpper)
                        && !snippet.ends_with('>')
                        && !generics.has_impl_trait()
                        && !self.tcx.fn_trait_kind_from_lang_item(def_id).is_some()
                    {
                        // FIXME: To avoid spurious suggestions in functions where type arguments
                        // where already supplied, we check the snippet to make sure it doesn't
                        // end with a turbofish. Ideally we would have access to a `PathSegment`
                        // instead. Otherwise we would produce the following output:
                        //
                        // error[E0283]: type annotations needed
                        //   --> $DIR/issue-54954.rs:3:24
                        //    |
                        // LL | const ARR_LEN: usize = Tt::const_val::<[i8; 123]>();
                        //    |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^
                        //    |                        |
                        //    |                        cannot infer type
                        //    |                        help: consider specifying the type argument
                        //    |                        in the function call:
                        //    |                        `Tt::const_val::<[i8; 123]>::<T>`
                        // ...
                        // LL |     const fn const_val<T: Sized>() -> usize {
                        //    |                        - required by this bound in `Tt::const_val`
                        //    |
                        //    = note: cannot satisfy `_: Tt`

                        // Clear any more general suggestions in favor of our specific one
                        err.clear_suggestions();

                        err.span_suggestion_verbose(
                            span.shrink_to_hi(),
                            &format!(
                                "consider specifying the type argument{} in the function call",
                                pluralize!(generics.params.len()),
                            ),
                            format!(
                                "::<{}>",
                                generics
                                    .params
                                    .iter()
                                    .map(|p| p.name.to_string())
                                    .collect::<Vec<String>>()
                                    .join(", ")
                            ),
                            Applicability::HasPlaceholders,
                        );
                    }
                }

                if let (Some(body_id), Some(ty::subst::GenericArgKind::Type(_))) =
                    (body_id, subst.map(|subst| subst.unpack()))
                {
                    struct FindExprBySpan<'hir> {
                        span: Span,
                        result: Option<&'hir hir::Expr<'hir>>,
                    }

                    impl<'v> hir::intravisit::Visitor<'v> for FindExprBySpan<'v> {
                        fn visit_expr(&mut self, ex: &'v hir::Expr<'v>) {
                            if self.span == ex.span {
                                self.result = Some(ex);
                            } else {
                                hir::intravisit::walk_expr(self, ex);
                            }
                        }
                    }

                    let mut expr_finder = FindExprBySpan { span, result: None };

                    expr_finder.visit_expr(&self.tcx.hir().body(body_id).value);

                    if let Some(hir::Expr {
                        kind: hir::ExprKind::Path(hir::QPath::Resolved(None, path)), .. }
                    ) = expr_finder.result
                        && let [
                            ..,
                            trait_path_segment @ hir::PathSegment {
                                res: rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Trait, trait_id),
                                ..
                            },
                            hir::PathSegment {
                                ident: assoc_item_name,
                                res: rustc_hir::def::Res::Def(_, item_id),
                                ..
                            }
                        ] = path.segments
                        && data.trait_ref.def_id == *trait_id
                        && self.tcx.trait_of_item(*item_id) == Some(*trait_id)
                        && !self.is_tainted_by_errors()
                    {
                        let (verb, noun) = match self.tcx.associated_item(item_id).kind {
                            ty::AssocKind::Const => ("refer to the", "constant"),
                            ty::AssocKind::Fn => ("call", "function"),
                            ty::AssocKind::Type => ("refer to the", "type"), // this is already covered by E0223, but this single match arm doesn't hurt here
                        };

                        // Replace the more general E0283 with a more specific error
                        err.cancel();
                        err = self.tcx.sess.struct_span_err_with_code(
                            span,
                            &format!(
                                "cannot {verb} associated {noun} on trait without specifying the corresponding `impl` type",
                             ),
                            rustc_errors::error_code!(E0790),
                        );

                        if let Some(local_def_id) = data.trait_ref.def_id.as_local()
                            && let Some(hir::Node::Item(hir::Item { ident: trait_name, kind: hir::ItemKind::Trait(_, _, _, _, trait_item_refs), .. })) = self.tcx.hir().find_by_def_id(local_def_id)
                            && let Some(method_ref) = trait_item_refs.iter().find(|item_ref| item_ref.ident == *assoc_item_name) {
                            err.span_label(method_ref.span, format!("`{}::{}` defined here", trait_name, assoc_item_name));
                        }

                        err.span_label(span, format!("cannot {verb} associated {noun} of trait"));

                        let trait_impls = self.tcx.trait_impls_of(data.trait_ref.def_id);

                        if trait_impls.blanket_impls().is_empty()
                            && let Some((impl_ty, _)) = trait_impls.non_blanket_impls().iter().next()
                            && let Some(impl_def_id) = impl_ty.def() {
                            let message = if trait_impls.non_blanket_impls().len() == 1 {
                                "use the fully-qualified path to the only available implementation".to_string()
                            } else {
                                format!(
                                    "use a fully-qualified path to a specific available implementation ({} found)",
                                    trait_impls.non_blanket_impls().len()
                                )
                            };
                            let mut suggestions = vec![(
                                trait_path_segment.ident.span.shrink_to_lo(),
                                format!("<{} as ", self.tcx.type_of(impl_def_id))
                            )];
                            if let Some(generic_arg) = trait_path_segment.args {
                                let between_span = trait_path_segment.ident.span.between(generic_arg.span_ext);
                                // get rid of :: between Trait and <type>
                                // must be '::' between them, otherwise the parser won't accept the code
                                suggestions.push((between_span, "".to_string(),));
                                suggestions.push((generic_arg.span_ext.shrink_to_hi(), format!(">")));
                            } else {
                                suggestions.push((trait_path_segment.ident.span.shrink_to_hi(), format!(">")));
                            }
                            err.multipart_suggestion(
                                message,
                                suggestions,
                                Applicability::MaybeIncorrect
                            );
                        }
                    }
                };

                err
            }

            ty::PredicateKind::WellFormed(arg) => {
                // Same hacky approach as above to avoid deluging user
                // with error messages.
                if arg.references_error()
                    || self.tcx.sess.has_errors().is_some()
                    || self.is_tainted_by_errors()
                {
                    return;
                }

                self.emit_inference_failure_err(body_id, span, arg, ErrorCode::E0282, false)
            }

            ty::PredicateKind::Subtype(data) => {
                if data.references_error()
                    || self.tcx.sess.has_errors().is_some()
                    || self.is_tainted_by_errors()
                {
                    // no need to overload user in such cases
                    return;
                }
                let SubtypePredicate { a_is_expected: _, a, b } = data;
                // both must be type variables, or the other would've been instantiated
                assert!(a.is_ty_var() && b.is_ty_var());
                self.emit_inference_failure_err(body_id, span, a.into(), ErrorCode::E0282, true)
            }
            ty::PredicateKind::Projection(data) => {
                if predicate.references_error() || self.is_tainted_by_errors() {
                    return;
                }
                let subst = data
                    .projection_ty
                    .substs
                    .iter()
                    .chain(Some(data.term.into_arg()))
                    .find(|g| g.has_non_region_infer());
                if let Some(subst) = subst {
                    let mut err = self.emit_inference_failure_err(
                        body_id,
                        span,
                        subst,
                        ErrorCode::E0284,
                        true,
                    );
                    err.note(&format!("cannot satisfy `{}`", predicate));
                    err
                } else {
                    // If we can't find a substitution, just print a generic error
                    let mut err = struct_span_err!(
                        self.tcx.sess,
                        span,
                        E0284,
                        "type annotations needed: cannot satisfy `{}`",
                        predicate,
                    );
                    err.span_label(span, &format!("cannot satisfy `{}`", predicate));
                    err
                }
            }

            ty::PredicateKind::ConstEvaluatable(data) => {
                if predicate.references_error() || self.is_tainted_by_errors() {
                    return;
                }
                let subst = data.walk().find(|g| g.is_non_region_infer());
                if let Some(subst) = subst {
                    let err = self.emit_inference_failure_err(
                        body_id,
                        span,
                        subst,
                        ErrorCode::E0284,
                        true,
                    );
                    err
                } else {
                    // If we can't find a substitution, just print a generic error
                    let mut err = struct_span_err!(
                        self.tcx.sess,
                        span,
                        E0284,
                        "type annotations needed: cannot satisfy `{}`",
                        predicate,
                    );
                    err.span_label(span, &format!("cannot satisfy `{}`", predicate));
                    err
                }
            }
            _ => {
                if self.tcx.sess.has_errors().is_some() || self.is_tainted_by_errors() {
                    return;
                }
                let mut err = struct_span_err!(
                    self.tcx.sess,
                    span,
                    E0284,
                    "type annotations needed: cannot satisfy `{}`",
                    predicate,
                );
                err.span_label(span, &format!("cannot satisfy `{}`", predicate));
                err
            }
        };
        self.note_obligation_cause(&mut err, obligation);
        err.emit();
    }

    fn annotate_source_of_ambiguity(
        &self,
        err: &mut Diagnostic,
        impls: &[DefId],
        predicate: ty::Predicate<'tcx>,
    ) {
        let mut spans = vec![];
        let mut crates = vec![];
        let mut post = vec![];
        for def_id in impls {
            match self.tcx.span_of_impl(*def_id) {
                Ok(span) => spans.push(span),
                Err(name) => {
                    crates.push(name);
                    if let Some(header) = to_pretty_impl_header(self.tcx, *def_id) {
                        post.push(header);
                    }
                }
            }
        }
        let msg = format!("multiple `impl`s satisfying `{}` found", predicate);
        let mut crate_names: Vec<_> = crates.iter().map(|n| format!("`{}`", n)).collect();
        crate_names.sort();
        crate_names.dedup();
        post.sort();
        post.dedup();

        if self.is_tainted_by_errors()
            && (crate_names.len() == 1
                && spans.len() == 0
                && ["`core`", "`alloc`", "`std`"].contains(&crate_names[0].as_str())
                || predicate.visit_with(&mut HasNumericInferVisitor).is_break())
        {
            // Avoid complaining about other inference issues for expressions like
            // `42 >> 1`, where the types are still `{integer}`, but we want to
            // Do we need `trait_ref.skip_binder().self_ty().is_numeric() &&` too?
            // NOTE(eddyb) this was `.cancel()`, but `err`
            // is borrowed, so we can't fully defuse it.
            err.downgrade_to_delayed_bug();
            return;
        }
        let post = if post.len() > 4 {
            format!(
                ":\n{}\nand {} more",
                post.iter().map(|p| format!("- {}", p)).take(4).collect::<Vec<_>>().join("\n"),
                post.len() - 4,
            )
        } else if post.len() > 1 || (post.len() == 1 && post[0].contains('\n')) {
            format!(":\n{}", post.iter().map(|p| format!("- {}", p)).collect::<Vec<_>>().join("\n"),)
        } else if post.len() == 1 {
            format!(": `{}`", post[0])
        } else {
            String::new()
        };

        match (spans.len(), crates.len(), crate_names.len()) {
            (0, 0, 0) => {
                err.note(&format!("cannot satisfy `{}`", predicate));
            }
            (0, _, 1) => {
                err.note(&format!("{} in the `{}` crate{}", msg, crates[0], post,));
            }
            (0, _, _) => {
                err.note(&format!(
                    "{} in the following crates: {}{}",
                    msg,
                    crate_names.join(", "),
                    post,
                ));
            }
            (_, 0, 0) => {
                let span: MultiSpan = spans.into();
                err.span_note(span, &msg);
            }
            (_, 1, 1) => {
                let span: MultiSpan = spans.into();
                err.span_note(span, &msg);
                err.note(
                    &format!("and another `impl` found in the `{}` crate{}", crates[0], post,),
                );
            }
            _ => {
                let span: MultiSpan = spans.into();
                err.span_note(span, &msg);
                err.note(&format!(
                    "and more `impl`s found in the following crates: {}{}",
                    crate_names.join(", "),
                    post,
                ));
            }
        }
    }

    /// Returns `true` if the trait predicate may apply for *some* assignment
    /// to the type parameters.
    fn predicate_can_apply(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        pred: ty::PolyTraitPredicate<'tcx>,
    ) -> bool {
        struct ParamToVarFolder<'a, 'tcx> {
            infcx: &'a InferCtxt<'tcx>,
            var_map: FxHashMap<Ty<'tcx>, Ty<'tcx>>,
        }

        impl<'a, 'tcx> TypeFolder<'tcx> for ParamToVarFolder<'a, 'tcx> {
            fn tcx<'b>(&'b self) -> TyCtxt<'tcx> {
                self.infcx.tcx
            }

            fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
                if let ty::Param(ty::ParamTy { name, .. }) = *ty.kind() {
                    let infcx = self.infcx;
                    *self.var_map.entry(ty).or_insert_with(|| {
                        infcx.next_ty_var(TypeVariableOrigin {
                            kind: TypeVariableOriginKind::TypeParameterDefinition(name, None),
                            span: DUMMY_SP,
                        })
                    })
                } else {
                    ty.super_fold_with(self)
                }
            }
        }

        self.probe(|_| {
            let mut selcx = SelectionContext::new(self);

            let cleaned_pred =
                pred.fold_with(&mut ParamToVarFolder { infcx: self, var_map: Default::default() });

            let cleaned_pred = super::project::normalize(
                &mut selcx,
                param_env,
                ObligationCause::dummy(),
                cleaned_pred,
            )
            .value;

            let obligation = Obligation::new(
                ObligationCause::dummy(),
                param_env,
                cleaned_pred.to_predicate(selcx.tcx()),
            );

            self.predicate_may_hold(&obligation)
        })
    }

    fn note_obligation_cause(&self, err: &mut Diagnostic, obligation: &PredicateObligation<'tcx>) {
        // First, attempt to add note to this error with an async-await-specific
        // message, and fall back to regular note otherwise.
        if !self.maybe_note_obligation_cause_for_async_await(err, obligation) {
            self.note_obligation_cause_code(
                err,
                &obligation.predicate,
                obligation.param_env,
                obligation.cause.code(),
                &mut vec![],
                &mut Default::default(),
            );
            self.suggest_unsized_bound_if_applicable(err, obligation);
        }
    }

    #[instrument(level = "debug", skip_all)]
    fn suggest_unsized_bound_if_applicable(
        &self,
        err: &mut Diagnostic,
        obligation: &PredicateObligation<'tcx>,
    ) {
        let ty::PredicateKind::Trait(pred) = obligation.predicate.kind().skip_binder() else { return; };
        let (ObligationCauseCode::BindingObligation(item_def_id, span)
        | ObligationCauseCode::ExprBindingObligation(item_def_id, span, ..))
            = *obligation.cause.code().peel_derives() else { return; };
        debug!(?pred, ?item_def_id, ?span);

        let (Some(node), true) = (
            self.tcx.hir().get_if_local(item_def_id),
            Some(pred.def_id()) == self.tcx.lang_items().sized_trait(),
        ) else {
            return;
        };
        self.maybe_suggest_unsized_generics(err, span, node);
    }

    #[instrument(level = "debug", skip_all)]
    fn maybe_suggest_unsized_generics(&self, err: &mut Diagnostic, span: Span, node: Node<'tcx>) {
        let Some(generics) = node.generics() else {
            return;
        };
        let sized_trait = self.tcx.lang_items().sized_trait();
        debug!(?generics.params);
        debug!(?generics.predicates);
        let Some(param) = generics.params.iter().find(|param| param.span == span) else {
            return;
        };
        let param_def_id = self.tcx.hir().local_def_id(param.hir_id);
        // Check that none of the explicit trait bounds is `Sized`. Assume that an explicit
        // `Sized` bound is there intentionally and we don't need to suggest relaxing it.
        let explicitly_sized = generics
            .bounds_for_param(param_def_id)
            .flat_map(|bp| bp.bounds)
            .any(|bound| bound.trait_ref().and_then(|tr| tr.trait_def_id()) == sized_trait);
        if explicitly_sized {
            return;
        }
        debug!(?param);
        match node {
            hir::Node::Item(
                item @ hir::Item {
                    // Only suggest indirection for uses of type parameters in ADTs.
                    kind:
                        hir::ItemKind::Enum(..) | hir::ItemKind::Struct(..) | hir::ItemKind::Union(..),
                    ..
                },
            ) => {
                if self.maybe_indirection_for_unsized(err, item, param) {
                    return;
                }
            }
            _ => {}
        };
        // Didn't add an indirection suggestion, so add a general suggestion to relax `Sized`.
        let (span, separator) = if let Some(s) = generics.bounds_span_for_suggestions(param_def_id)
        {
            (s, " +")
        } else {
            (span.shrink_to_hi(), ":")
        };
        err.span_suggestion_verbose(
            span,
            "consider relaxing the implicit `Sized` restriction",
            format!("{} ?Sized", separator),
            Applicability::MachineApplicable,
        );
    }

    fn maybe_indirection_for_unsized(
        &self,
        err: &mut Diagnostic,
        item: &Item<'tcx>,
        param: &GenericParam<'tcx>,
    ) -> bool {
        // Suggesting `T: ?Sized` is only valid in an ADT if `T` is only used in a
        // borrow. `struct S<'a, T: ?Sized>(&'a T);` is valid, `struct S<T: ?Sized>(T);`
        // is not. Look for invalid "bare" parameter uses, and suggest using indirection.
        let mut visitor =
            FindTypeParam { param: param.name.ident().name, invalid_spans: vec![], nested: false };
        visitor.visit_item(item);
        if visitor.invalid_spans.is_empty() {
            return false;
        }
        let mut multispan: MultiSpan = param.span.into();
        multispan.push_span_label(
            param.span,
            format!("this could be changed to `{}: ?Sized`...", param.name.ident()),
        );
        for sp in visitor.invalid_spans {
            multispan.push_span_label(
                sp,
                format!("...if indirection were used here: `Box<{}>`", param.name.ident()),
            );
        }
        err.span_help(
            multispan,
            &format!(
                "you could relax the implicit `Sized` bound on `{T}` if it were \
                used through indirection like `&{T}` or `Box<{T}>`",
                T = param.name.ident(),
            ),
        );
        true
    }

    fn is_recursive_obligation(
        &self,
        obligated_types: &mut Vec<Ty<'tcx>>,
        cause_code: &ObligationCauseCode<'tcx>,
    ) -> bool {
        if let ObligationCauseCode::BuiltinDerivedObligation(ref data) = cause_code {
            let parent_trait_ref = self.resolve_vars_if_possible(data.parent_trait_pred);
            let self_ty = parent_trait_ref.skip_binder().self_ty();
            if obligated_types.iter().any(|ot| ot == &self_ty) {
                return true;
            }
            if let ty::Adt(def, substs) = self_ty.kind()
                && let [arg] = &substs[..]
                && let ty::subst::GenericArgKind::Type(ty) = arg.unpack()
                && let ty::Adt(inner_def, _) = ty.kind()
                && inner_def == def
            {
                return true;
            }
        }
        false
    }
}

/// Look for type `param` in an ADT being used only through a reference to confirm that suggesting
/// `param: ?Sized` would be a valid constraint.
struct FindTypeParam {
    param: rustc_span::Symbol,
    invalid_spans: Vec<Span>,
    nested: bool,
}

impl<'v> Visitor<'v> for FindTypeParam {
    fn visit_where_predicate(&mut self, _: &'v hir::WherePredicate<'v>) {
        // Skip where-clauses, to avoid suggesting indirection for type parameters found there.
    }

    fn visit_ty(&mut self, ty: &hir::Ty<'_>) {
        // We collect the spans of all uses of the "bare" type param, like in `field: T` or
        // `field: (T, T)` where we could make `T: ?Sized` while skipping cases that are known to be
        // valid like `field: &'a T` or `field: *mut T` and cases that *might* have further `Sized`
        // obligations like `Box<T>` and `Vec<T>`, but we perform no extra analysis for those cases
        // and suggest `T: ?Sized` regardless of their obligations. This is fine because the errors
        // in that case should make what happened clear enough.
        match ty.kind {
            hir::TyKind::Ptr(_) | hir::TyKind::Rptr(..) | hir::TyKind::TraitObject(..) => {}
            hir::TyKind::Path(hir::QPath::Resolved(None, path))
                if path.segments.len() == 1 && path.segments[0].ident.name == self.param =>
            {
                if !self.nested {
                    debug!(?ty, "FindTypeParam::visit_ty");
                    self.invalid_spans.push(ty.span);
                }
            }
            hir::TyKind::Path(_) => {
                let prev = self.nested;
                self.nested = true;
                hir::intravisit::walk_ty(self, ty);
                self.nested = prev;
            }
            _ => {
                hir::intravisit::walk_ty(self, ty);
            }
        }
    }
}

/// Summarizes information
#[derive(Clone)]
pub enum ArgKind {
    /// An argument of non-tuple type. Parameters are (name, ty)
    Arg(String, String),

    /// An argument of tuple type. For a "found" argument, the span is
    /// the location in the source of the pattern. For an "expected"
    /// argument, it will be None. The vector is a list of (name, ty)
    /// strings for the components of the tuple.
    Tuple(Option<Span>, Vec<(String, String)>),
}

impl ArgKind {
    fn empty() -> ArgKind {
        ArgKind::Arg("_".to_owned(), "_".to_owned())
    }

    /// Creates an `ArgKind` from the expected type of an
    /// argument. It has no name (`_`) and an optional source span.
    pub fn from_expected_ty(t: Ty<'_>, span: Option<Span>) -> ArgKind {
        match t.kind() {
            ty::Tuple(tys) => ArgKind::Tuple(
                span,
                tys.iter().map(|ty| ("_".to_owned(), ty.to_string())).collect::<Vec<_>>(),
            ),
            _ => ArgKind::Arg("_".to_owned(), t.to_string()),
        }
    }
}

struct HasNumericInferVisitor;

impl<'tcx> ty::TypeVisitor<'tcx> for HasNumericInferVisitor {
    type BreakTy = ();

    fn visit_ty(&mut self, ty: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if matches!(ty.kind(), ty::Infer(ty::FloatVar(_) | ty::IntVar(_))) {
            ControlFlow::Break(())
        } else {
            ControlFlow::CONTINUE
        }
    }
}

pub enum DefIdOrName {
    DefId(DefId),
    Name(&'static str),
}
