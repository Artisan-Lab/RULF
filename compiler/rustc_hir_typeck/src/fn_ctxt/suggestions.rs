use super::FnCtxt;

use crate::errors::{AddReturnTypeSuggestion, ExpectedReturnTypeLabel};
use rustc_ast::util::parser::{ExprPrecedence, PREC_POSTFIX};
use rustc_errors::{Applicability, Diagnostic, MultiSpan};
use rustc_hir as hir;
use rustc_hir::def::{CtorOf, DefKind};
use rustc_hir::lang_items::LangItem;
use rustc_hir::{
    Expr, ExprKind, GenericBound, Node, Path, QPath, Stmt, StmtKind, TyKind, WherePredicate,
};
use rustc_hir_analysis::astconv::AstConv;
use rustc_infer::infer::{self, TyCtxtInferExt};
use rustc_infer::traits::{self, StatementAsExpression};
use rustc_middle::lint::in_external_macro;
use rustc_middle::ty::{self, Binder, IsSuggestable, ToPredicate, Ty};
use rustc_session::errors::ExprParenthesesNeeded;
use rustc_span::symbol::sym;
use rustc_span::Span;
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_trait_selection::traits::error_reporting::DefIdOrName;
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;

impl<'a, 'tcx> FnCtxt<'a, 'tcx> {
    pub(in super::super) fn suggest_semicolon_at_end(&self, span: Span, err: &mut Diagnostic) {
        err.span_suggestion_short(
            span.shrink_to_hi(),
            "consider using a semicolon here",
            ";",
            Applicability::MachineApplicable,
        );
    }

    /// On implicit return expressions with mismatched types, provides the following suggestions:
    ///
    /// - Points out the method's return type as the reason for the expected type.
    /// - Possible missing semicolon.
    /// - Possible missing return type if the return type is the default, and not `fn main()`.
    pub fn suggest_mismatched_types_on_tail(
        &self,
        err: &mut Diagnostic,
        expr: &'tcx hir::Expr<'tcx>,
        expected: Ty<'tcx>,
        found: Ty<'tcx>,
        blk_id: hir::HirId,
    ) -> bool {
        let expr = expr.peel_drop_temps();
        self.suggest_missing_semicolon(err, expr, expected, false);
        let mut pointing_at_return_type = false;
        if let Some((fn_decl, can_suggest)) = self.get_fn_decl(blk_id) {
            let fn_id = self.tcx.hir().get_return_block(blk_id).unwrap();
            pointing_at_return_type = self.suggest_missing_return_type(
                err,
                &fn_decl,
                expected,
                found,
                can_suggest,
                fn_id,
            );
            self.suggest_missing_break_or_return_expr(
                err, expr, &fn_decl, expected, found, blk_id, fn_id,
            );
        }
        pointing_at_return_type
    }

    /// When encountering an fn-like type, try accessing the output of the type
    /// and suggesting calling it if it satisfies a predicate (i.e. if the
    /// output has a method or a field):
    /// ```compile_fail,E0308
    /// fn foo(x: usize) -> usize { x }
    /// let x: usize = foo;  // suggest calling the `foo` function: `foo(42)`
    /// ```
    pub(crate) fn suggest_fn_call(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'_>,
        found: Ty<'tcx>,
        can_satisfy: impl FnOnce(Ty<'tcx>) -> bool,
    ) -> bool {
        let Some((def_id_or_name, output, inputs)) = self.extract_callable_info(expr, found)
            else { return false; };
        if can_satisfy(output) {
            let (sugg_call, mut applicability) = match inputs.len() {
                0 => ("".to_string(), Applicability::MachineApplicable),
                1..=4 => (
                    inputs
                        .iter()
                        .map(|ty| {
                            if ty.is_suggestable(self.tcx, false) {
                                format!("/* {ty} */")
                            } else {
                                "/* value */".to_string()
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(", "),
                    Applicability::HasPlaceholders,
                ),
                _ => ("/* ... */".to_string(), Applicability::HasPlaceholders),
            };

            let msg = match def_id_or_name {
                DefIdOrName::DefId(def_id) => match self.tcx.def_kind(def_id) {
                    DefKind::Ctor(CtorOf::Struct, _) => "construct this tuple struct".to_string(),
                    DefKind::Ctor(CtorOf::Variant, _) => "construct this tuple variant".to_string(),
                    kind => format!("call this {}", kind.descr(def_id)),
                },
                DefIdOrName::Name(name) => format!("call this {name}"),
            };

            let sugg = match expr.kind {
                hir::ExprKind::Call(..)
                | hir::ExprKind::Path(..)
                | hir::ExprKind::Index(..)
                | hir::ExprKind::Lit(..) => {
                    vec![(expr.span.shrink_to_hi(), format!("({sugg_call})"))]
                }
                hir::ExprKind::Closure { .. } => {
                    // Might be `{ expr } || { bool }`
                    applicability = Applicability::MaybeIncorrect;
                    vec![
                        (expr.span.shrink_to_lo(), "(".to_string()),
                        (expr.span.shrink_to_hi(), format!(")({sugg_call})")),
                    ]
                }
                _ => {
                    vec![
                        (expr.span.shrink_to_lo(), "(".to_string()),
                        (expr.span.shrink_to_hi(), format!(")({sugg_call})")),
                    ]
                }
            };

            err.multipart_suggestion_verbose(
                format!("use parentheses to {msg}"),
                sugg,
                applicability,
            );
            return true;
        }
        false
    }

    /// Extracts information about a callable type for diagnostics. This is a
    /// heuristic -- it doesn't necessarily mean that a type is always callable,
    /// because the callable type must also be well-formed to be called.
    pub(in super::super) fn extract_callable_info(
        &self,
        expr: &Expr<'_>,
        found: Ty<'tcx>,
    ) -> Option<(DefIdOrName, Ty<'tcx>, Vec<Ty<'tcx>>)> {
        // Autoderef is useful here because sometimes we box callables, etc.
        let Some((def_id_or_name, output, inputs)) = self.autoderef(expr.span, found).silence_errors().find_map(|(found, _)| {
            match *found.kind() {
                ty::FnPtr(fn_sig) =>
                    Some((DefIdOrName::Name("function pointer"), fn_sig.output(), fn_sig.inputs())),
                ty::FnDef(def_id, _) => {
                    let fn_sig = found.fn_sig(self.tcx);
                    Some((DefIdOrName::DefId(def_id), fn_sig.output(), fn_sig.inputs()))
                }
                ty::Closure(def_id, substs) => {
                    let fn_sig = substs.as_closure().sig();
                    Some((DefIdOrName::DefId(def_id), fn_sig.output(), fn_sig.inputs().map_bound(|inputs| &inputs[1..])))
                }
                ty::Opaque(def_id, substs) => {
                    self.tcx.bound_item_bounds(def_id).subst(self.tcx, substs).iter().find_map(|pred| {
                        if let ty::PredicateKind::Projection(proj) = pred.kind().skip_binder()
                        && Some(proj.projection_ty.item_def_id) == self.tcx.lang_items().fn_once_output()
                        // args tuple will always be substs[1]
                        && let ty::Tuple(args) = proj.projection_ty.substs.type_at(1).kind()
                        {
                            Some((
                                DefIdOrName::DefId(def_id),
                                pred.kind().rebind(proj.term.ty().unwrap()),
                                pred.kind().rebind(args.as_slice()),
                            ))
                        } else {
                            None
                        }
                    })
                }
                ty::Dynamic(data, _, ty::Dyn) => {
                    data.iter().find_map(|pred| {
                        if let ty::ExistentialPredicate::Projection(proj) = pred.skip_binder()
                        && Some(proj.item_def_id) == self.tcx.lang_items().fn_once_output()
                        // for existential projection, substs are shifted over by 1
                        && let ty::Tuple(args) = proj.substs.type_at(0).kind()
                        {
                            Some((
                                DefIdOrName::Name("trait object"),
                                pred.rebind(proj.term.ty().unwrap()),
                                pred.rebind(args.as_slice()),
                            ))
                        } else {
                            None
                        }
                    })
                }
                ty::Param(param) => {
                    let def_id = self.tcx.generics_of(self.body_id.owner).type_param(&param, self.tcx).def_id;
                    self.tcx.predicates_of(self.body_id.owner).predicates.iter().find_map(|(pred, _)| {
                        if let ty::PredicateKind::Projection(proj) = pred.kind().skip_binder()
                        && Some(proj.projection_ty.item_def_id) == self.tcx.lang_items().fn_once_output()
                        && proj.projection_ty.self_ty() == found
                        // args tuple will always be substs[1]
                        && let ty::Tuple(args) = proj.projection_ty.substs.type_at(1).kind()
                        {
                            Some((
                                DefIdOrName::DefId(def_id),
                                pred.kind().rebind(proj.term.ty().unwrap()),
                                pred.kind().rebind(args.as_slice()),
                            ))
                        } else {
                            None
                        }
                    })
                }
                _ => None,
            }
        }) else { return None; };

        let output = self.replace_bound_vars_with_fresh_vars(expr.span, infer::FnCall, output);
        let inputs = inputs
            .skip_binder()
            .iter()
            .map(|ty| {
                self.replace_bound_vars_with_fresh_vars(
                    expr.span,
                    infer::FnCall,
                    inputs.rebind(*ty),
                )
            })
            .collect();

        // We don't want to register any extra obligations, which should be
        // implied by wf, but also because that would possibly result in
        // erroneous errors later on.
        let infer::InferOk { value: output, obligations: _ } =
            self.normalize_associated_types_in_as_infer_ok(expr.span, output);

        if output.is_ty_var() { None } else { Some((def_id_or_name, output, inputs)) }
    }

    pub fn suggest_two_fn_call(
        &self,
        err: &mut Diagnostic,
        lhs_expr: &'tcx hir::Expr<'tcx>,
        lhs_ty: Ty<'tcx>,
        rhs_expr: &'tcx hir::Expr<'tcx>,
        rhs_ty: Ty<'tcx>,
        can_satisfy: impl FnOnce(Ty<'tcx>, Ty<'tcx>) -> bool,
    ) -> bool {
        let Some((_, lhs_output_ty, lhs_inputs)) = self.extract_callable_info(lhs_expr, lhs_ty)
            else { return false; };
        let Some((_, rhs_output_ty, rhs_inputs)) = self.extract_callable_info(rhs_expr, rhs_ty)
            else { return false; };

        if can_satisfy(lhs_output_ty, rhs_output_ty) {
            let mut sugg = vec![];
            let mut applicability = Applicability::MachineApplicable;

            for (expr, inputs) in [(lhs_expr, lhs_inputs), (rhs_expr, rhs_inputs)] {
                let (sugg_call, this_applicability) = match inputs.len() {
                    0 => ("".to_string(), Applicability::MachineApplicable),
                    1..=4 => (
                        inputs
                            .iter()
                            .map(|ty| {
                                if ty.is_suggestable(self.tcx, false) {
                                    format!("/* {ty} */")
                                } else {
                                    "/* value */".to_string()
                                }
                            })
                            .collect::<Vec<_>>()
                            .join(", "),
                        Applicability::HasPlaceholders,
                    ),
                    _ => ("/* ... */".to_string(), Applicability::HasPlaceholders),
                };

                applicability = applicability.max(this_applicability);

                match expr.kind {
                    hir::ExprKind::Call(..)
                    | hir::ExprKind::Path(..)
                    | hir::ExprKind::Index(..)
                    | hir::ExprKind::Lit(..) => {
                        sugg.extend([(expr.span.shrink_to_hi(), format!("({sugg_call})"))]);
                    }
                    hir::ExprKind::Closure { .. } => {
                        // Might be `{ expr } || { bool }`
                        applicability = Applicability::MaybeIncorrect;
                        sugg.extend([
                            (expr.span.shrink_to_lo(), "(".to_string()),
                            (expr.span.shrink_to_hi(), format!(")({sugg_call})")),
                        ]);
                    }
                    _ => {
                        sugg.extend([
                            (expr.span.shrink_to_lo(), "(".to_string()),
                            (expr.span.shrink_to_hi(), format!(")({sugg_call})")),
                        ]);
                    }
                }
            }

            err.multipart_suggestion_verbose(
                format!("use parentheses to call these"),
                sugg,
                applicability,
            );

            true
        } else {
            false
        }
    }

    pub fn suggest_deref_ref_or_into(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'tcx>,
        expected: Ty<'tcx>,
        found: Ty<'tcx>,
        expected_ty_expr: Option<&'tcx hir::Expr<'tcx>>,
    ) -> bool {
        let expr = expr.peel_blocks();
        if let Some((sp, msg, suggestion, applicability, verbose, annotation)) =
            self.check_ref(expr, found, expected)
        {
            if verbose {
                err.span_suggestion_verbose(sp, &msg, suggestion, applicability);
            } else {
                err.span_suggestion(sp, &msg, suggestion, applicability);
            }
            if annotation {
                let suggest_annotation = match expr.peel_drop_temps().kind {
                    hir::ExprKind::AddrOf(hir::BorrowKind::Ref, hir::Mutability::Not, _) => "&",
                    hir::ExprKind::AddrOf(hir::BorrowKind::Ref, hir::Mutability::Mut, _) => "&mut ",
                    _ => return true,
                };
                let mut tuple_indexes = Vec::new();
                let mut expr_id = expr.hir_id;
                for (parent_id, node) in self.tcx.hir().parent_iter(expr.hir_id) {
                    match node {
                        Node::Expr(&Expr { kind: ExprKind::Tup(subs), .. }) => {
                            tuple_indexes.push(
                                subs.iter()
                                    .enumerate()
                                    .find(|(_, sub_expr)| sub_expr.hir_id == expr_id)
                                    .unwrap()
                                    .0,
                            );
                            expr_id = parent_id;
                        }
                        Node::Local(local) => {
                            if let Some(mut ty) = local.ty {
                                while let Some(index) = tuple_indexes.pop() {
                                    match ty.kind {
                                        TyKind::Tup(tys) => ty = &tys[index],
                                        _ => return true,
                                    }
                                }
                                let annotation_span = ty.span;
                                err.span_suggestion(
                                    annotation_span.with_hi(annotation_span.lo()),
                                    format!("alternatively, consider changing the type annotation"),
                                    suggest_annotation,
                                    Applicability::MaybeIncorrect,
                                );
                            }
                            break;
                        }
                        _ => break,
                    }
                }
            }
            return true;
        } else if self.suggest_else_fn_with_closure(err, expr, found, expected) {
            return true;
        } else if self.suggest_fn_call(err, expr, found, |output| self.can_coerce(output, expected))
            && let ty::FnDef(def_id, ..) = &found.kind()
            && let Some(sp) = self.tcx.hir().span_if_local(*def_id)
        {
            err.span_label(sp, format!("{found} defined here"));
            return true;
        } else if self.check_for_cast(err, expr, found, expected, expected_ty_expr) {
            return true;
        } else {
            let methods = self.get_conversion_methods(expr.span, expected, found, expr.hir_id);
            if !methods.is_empty() {
                let mut suggestions = methods.iter()
                    .filter_map(|conversion_method| {
                        let receiver_method_ident = expr.method_ident();
                        if let Some(method_ident) = receiver_method_ident
                            && method_ident.name == conversion_method.name
                        {
                            return None // do not suggest code that is already there (#53348)
                        }

                        let method_call_list = [sym::to_vec, sym::to_string];
                        let mut sugg = if let ExprKind::MethodCall(receiver_method, ..) = expr.kind
                            && receiver_method.ident.name == sym::clone
                            && method_call_list.contains(&conversion_method.name)
                            // If receiver is `.clone()` and found type has one of those methods,
                            // we guess that the user wants to convert from a slice type (`&[]` or `&str`)
                            // to an owned type (`Vec` or `String`).  These conversions clone internally,
                            // so we remove the user's `clone` call.
                        {
                            vec![(
                                receiver_method.ident.span,
                                conversion_method.name.to_string()
                            )]
                        } else if expr.precedence().order()
                            < ExprPrecedence::MethodCall.order()
                        {
                            vec![
                                (expr.span.shrink_to_lo(), "(".to_string()),
                                (expr.span.shrink_to_hi(), format!(").{}()", conversion_method.name)),
                            ]
                        } else {
                            vec![(expr.span.shrink_to_hi(), format!(".{}()", conversion_method.name))]
                        };
                        let struct_pat_shorthand_field = self.maybe_get_struct_pattern_shorthand_field(expr);
                        if let Some(name) = struct_pat_shorthand_field {
                            sugg.insert(
                                0,
                                (expr.span.shrink_to_lo(), format!("{}: ", name)),
                            );
                        }
                        Some(sugg)
                    })
                    .peekable();
                if suggestions.peek().is_some() {
                    err.multipart_suggestions(
                        "try using a conversion method",
                        suggestions,
                        Applicability::MaybeIncorrect,
                    );
                    return true;
                }
            } else if let ty::Adt(found_adt, found_substs) = found.kind()
                && self.tcx.is_diagnostic_item(sym::Option, found_adt.did())
                && let ty::Adt(expected_adt, expected_substs) = expected.kind()
                && self.tcx.is_diagnostic_item(sym::Option, expected_adt.did())
                && let ty::Ref(_, inner_ty, _) = expected_substs.type_at(0).kind()
                && inner_ty.is_str()
            {
                let ty = found_substs.type_at(0);
                let mut peeled = ty;
                let mut ref_cnt = 0;
                while let ty::Ref(_, inner, _) = peeled.kind() {
                    peeled = *inner;
                    ref_cnt += 1;
                }
                if let ty::Adt(adt, _) = peeled.kind()
                    && self.tcx.is_diagnostic_item(sym::String, adt.did())
                {
                    err.span_suggestion_verbose(
                        expr.span.shrink_to_hi(),
                        "try converting the passed type into a `&str`",
                        format!(".map(|x| &*{}x)", "*".repeat(ref_cnt)),
                        Applicability::MaybeIncorrect,
                    );
                    return true;
                }
            }
        }

        false
    }

    /// When encountering the expected boxed value allocated in the stack, suggest allocating it
    /// in the heap by calling `Box::new()`.
    pub(in super::super) fn suggest_boxing_when_appropriate(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'_>,
        expected: Ty<'tcx>,
        found: Ty<'tcx>,
    ) -> bool {
        if self.tcx.hir().is_inside_const_context(expr.hir_id) {
            // Do not suggest `Box::new` in const context.
            return false;
        }
        if !expected.is_box() || found.is_box() {
            return false;
        }
        let boxed_found = self.tcx.mk_box(found);
        if self.can_coerce(boxed_found, expected) {
            err.multipart_suggestion(
                "store this in the heap by calling `Box::new`",
                vec![
                    (expr.span.shrink_to_lo(), "Box::new(".to_string()),
                    (expr.span.shrink_to_hi(), ")".to_string()),
                ],
                Applicability::MachineApplicable,
            );
            err.note(
                "for more on the distinction between the stack and the heap, read \
                 https://doc.rust-lang.org/book/ch15-01-box.html, \
                 https://doc.rust-lang.org/rust-by-example/std/box.html, and \
                 https://doc.rust-lang.org/std/boxed/index.html",
            );
            true
        } else {
            false
        }
    }

    /// When encountering a closure that captures variables, where a FnPtr is expected,
    /// suggest a non-capturing closure
    pub(in super::super) fn suggest_no_capture_closure(
        &self,
        err: &mut Diagnostic,
        expected: Ty<'tcx>,
        found: Ty<'tcx>,
    ) -> bool {
        if let (ty::FnPtr(_), ty::Closure(def_id, _)) = (expected.kind(), found.kind()) {
            if let Some(upvars) = self.tcx.upvars_mentioned(*def_id) {
                // Report upto four upvars being captured to reduce the amount error messages
                // reported back to the user.
                let spans_and_labels = upvars
                    .iter()
                    .take(4)
                    .map(|(var_hir_id, upvar)| {
                        let var_name = self.tcx.hir().name(*var_hir_id).to_string();
                        let msg = format!("`{}` captured here", var_name);
                        (upvar.span, msg)
                    })
                    .collect::<Vec<_>>();

                let mut multi_span: MultiSpan =
                    spans_and_labels.iter().map(|(sp, _)| *sp).collect::<Vec<_>>().into();
                for (sp, label) in spans_and_labels {
                    multi_span.push_span_label(sp, label);
                }
                err.span_note(
                    multi_span,
                    "closures can only be coerced to `fn` types if they do not capture any variables"
                );
                return true;
            }
        }
        false
    }

    /// When encountering an `impl Future` where `BoxFuture` is expected, suggest `Box::pin`.
    #[instrument(skip(self, err))]
    pub(in super::super) fn suggest_calling_boxed_future_when_appropriate(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'_>,
        expected: Ty<'tcx>,
        found: Ty<'tcx>,
    ) -> bool {
        // Handle #68197.

        if self.tcx.hir().is_inside_const_context(expr.hir_id) {
            // Do not suggest `Box::new` in const context.
            return false;
        }
        let pin_did = self.tcx.lang_items().pin_type();
        // This guards the `unwrap` and `mk_box` below.
        if pin_did.is_none() || self.tcx.lang_items().owned_box().is_none() {
            return false;
        }
        let box_found = self.tcx.mk_box(found);
        let pin_box_found = self.tcx.mk_lang_item(box_found, LangItem::Pin).unwrap();
        let pin_found = self.tcx.mk_lang_item(found, LangItem::Pin).unwrap();
        match expected.kind() {
            ty::Adt(def, _) if Some(def.did()) == pin_did => {
                if self.can_coerce(pin_box_found, expected) {
                    debug!("can coerce {:?} to {:?}, suggesting Box::pin", pin_box_found, expected);
                    match found.kind() {
                        ty::Adt(def, _) if def.is_box() => {
                            err.help("use `Box::pin`");
                        }
                        _ => {
                            err.multipart_suggestion(
                                "you need to pin and box this expression",
                                vec![
                                    (expr.span.shrink_to_lo(), "Box::pin(".to_string()),
                                    (expr.span.shrink_to_hi(), ")".to_string()),
                                ],
                                Applicability::MaybeIncorrect,
                            );
                        }
                    }
                    true
                } else if self.can_coerce(pin_found, expected) {
                    match found.kind() {
                        ty::Adt(def, _) if def.is_box() => {
                            err.help("use `Box::pin`");
                            true
                        }
                        _ => false,
                    }
                } else {
                    false
                }
            }
            ty::Adt(def, _) if def.is_box() && self.can_coerce(box_found, expected) => {
                // Check if the parent expression is a call to Pin::new.  If it
                // is and we were expecting a Box, ergo Pin<Box<expected>>, we
                // can suggest Box::pin.
                let parent = self.tcx.hir().get_parent_node(expr.hir_id);
                let Some(Node::Expr(Expr { kind: ExprKind::Call(fn_name, _), .. })) = self.tcx.hir().find(parent) else {
                    return false;
                };
                match fn_name.kind {
                    ExprKind::Path(QPath::TypeRelative(
                        hir::Ty {
                            kind: TyKind::Path(QPath::Resolved(_, Path { res: recv_ty, .. })),
                            ..
                        },
                        method,
                    )) if recv_ty.opt_def_id() == pin_did && method.ident.name == sym::new => {
                        err.span_suggestion(
                            fn_name.span,
                            "use `Box::pin` to pin and box this expression",
                            "Box::pin",
                            Applicability::MachineApplicable,
                        );
                        true
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// A common error is to forget to add a semicolon at the end of a block, e.g.,
    ///
    /// ```compile_fail,E0308
    /// # fn bar_that_returns_u32() -> u32 { 4 }
    /// fn foo() {
    ///     bar_that_returns_u32()
    /// }
    /// ```
    ///
    /// This routine checks if the return expression in a block would make sense on its own as a
    /// statement and the return type has been left as default or has been specified as `()`. If so,
    /// it suggests adding a semicolon.
    ///
    /// If the expression is the expression of a closure without block (`|| expr`), a
    /// block is needed to be added too (`|| { expr; }`). This is denoted by `needs_block`.
    pub fn suggest_missing_semicolon(
        &self,
        err: &mut Diagnostic,
        expression: &'tcx hir::Expr<'tcx>,
        expected: Ty<'tcx>,
        needs_block: bool,
    ) {
        if expected.is_unit() {
            // `BlockTailExpression` only relevant if the tail expr would be
            // useful on its own.
            match expression.kind {
                ExprKind::Call(..)
                | ExprKind::MethodCall(..)
                | ExprKind::Loop(..)
                | ExprKind::If(..)
                | ExprKind::Match(..)
                | ExprKind::Block(..)
                    if expression.can_have_side_effects()
                        // If the expression is from an external macro, then do not suggest
                        // adding a semicolon, because there's nowhere to put it.
                        // See issue #81943.
                        && !in_external_macro(self.tcx.sess, expression.span) =>
                {
                    if needs_block {
                        err.multipart_suggestion(
                            "consider using a semicolon here",
                            vec![
                                (expression.span.shrink_to_lo(), "{ ".to_owned()),
                                (expression.span.shrink_to_hi(), "; }".to_owned()),
                            ],
                            Applicability::MachineApplicable,
                        );
                    } else {
                        err.span_suggestion(
                            expression.span.shrink_to_hi(),
                            "consider using a semicolon here",
                            ";",
                            Applicability::MachineApplicable,
                        );
                    }
                }
                _ => (),
            }
        }
    }

    /// A possible error is to forget to add a return type that is needed:
    ///
    /// ```compile_fail,E0308
    /// # fn bar_that_returns_u32() -> u32 { 4 }
    /// fn foo() {
    ///     bar_that_returns_u32()
    /// }
    /// ```
    ///
    /// This routine checks if the return type is left as default, the method is not part of an
    /// `impl` block and that it isn't the `main` method. If so, it suggests setting the return
    /// type.
    pub(in super::super) fn suggest_missing_return_type(
        &self,
        err: &mut Diagnostic,
        fn_decl: &hir::FnDecl<'_>,
        expected: Ty<'tcx>,
        found: Ty<'tcx>,
        can_suggest: bool,
        fn_id: hir::HirId,
    ) -> bool {
        let found =
            self.resolve_numeric_literals_with_default(self.resolve_vars_if_possible(found));
        // Only suggest changing the return type for methods that
        // haven't set a return type at all (and aren't `fn main()` or an impl).
        match &fn_decl.output {
            &hir::FnRetTy::DefaultReturn(span) if expected.is_unit() && !can_suggest => {
                // `fn main()` must return `()`, do not suggest changing return type
                err.subdiagnostic(ExpectedReturnTypeLabel::Unit { span });
                return true;
            }
            &hir::FnRetTy::DefaultReturn(span) if expected.is_unit() => {
                if found.is_suggestable(self.tcx, false) {
                    err.subdiagnostic(AddReturnTypeSuggestion::Add { span, found: found.to_string() });
                    return true;
                } else if let ty::Closure(_, substs) = found.kind()
                    // FIXME(compiler-errors): Get better at printing binders...
                    && let closure = substs.as_closure()
                    && closure.sig().is_suggestable(self.tcx, false)
                {
                    err.subdiagnostic(AddReturnTypeSuggestion::Add { span, found: closure.print_as_impl_trait().to_string() });
                    return true;
                } else {
                    // FIXME: if `found` could be `impl Iterator` we should suggest that.
                    err.subdiagnostic(AddReturnTypeSuggestion::MissingHere { span });
                    return true
                }
            }
            &hir::FnRetTy::Return(ref ty) => {
                // Only point to return type if the expected type is the return type, as if they
                // are not, the expectation must have been caused by something else.
                debug!("suggest_missing_return_type: return type {:?} node {:?}", ty, ty.kind);
                let span = ty.span;
                let ty = <dyn AstConv<'_>>::ast_ty_to_ty(self, ty);
                debug!("suggest_missing_return_type: return type {:?}", ty);
                debug!("suggest_missing_return_type: expected type {:?}", ty);
                let bound_vars = self.tcx.late_bound_vars(fn_id);
                let ty = Binder::bind_with_vars(ty, bound_vars);
                let ty = self.normalize_associated_types_in(span, ty);
                let ty = self.tcx.erase_late_bound_regions(ty);
                if self.can_coerce(expected, ty) {
                    err.subdiagnostic(ExpectedReturnTypeLabel::Other { span, expected });
                    self.try_suggest_return_impl_trait(err, expected, ty, fn_id);
                    return true;
                }
            }
            _ => {}
        }
        false
    }

    /// check whether the return type is a generic type with a trait bound
    /// only suggest this if the generic param is not present in the arguments
    /// if this is true, hint them towards changing the return type to `impl Trait`
    /// ```compile_fail,E0308
    /// fn cant_name_it<T: Fn() -> u32>() -> T {
    ///     || 3
    /// }
    /// ```
    fn try_suggest_return_impl_trait(
        &self,
        err: &mut Diagnostic,
        expected: Ty<'tcx>,
        found: Ty<'tcx>,
        fn_id: hir::HirId,
    ) {
        // Only apply the suggestion if:
        //  - the return type is a generic parameter
        //  - the generic param is not used as a fn param
        //  - the generic param has at least one bound
        //  - the generic param doesn't appear in any other bounds where it's not the Self type
        // Suggest:
        //  - Changing the return type to be `impl <all bounds>`

        debug!("try_suggest_return_impl_trait, expected = {:?}, found = {:?}", expected, found);

        let ty::Param(expected_ty_as_param) = expected.kind() else { return };

        let fn_node = self.tcx.hir().find(fn_id);

        let Some(hir::Node::Item(hir::Item {
            kind:
                hir::ItemKind::Fn(
                    hir::FnSig { decl: hir::FnDecl { inputs: fn_parameters, output: fn_return, .. }, .. },
                    hir::Generics { params, predicates, .. },
                    _body_id,
                ),
            ..
        })) = fn_node else { return };

        if params.get(expected_ty_as_param.index as usize).is_none() {
            return;
        };

        // get all where BoundPredicates here, because they are used in to cases below
        let where_predicates = predicates
            .iter()
            .filter_map(|p| match p {
                WherePredicate::BoundPredicate(hir::WhereBoundPredicate {
                    bounds,
                    bounded_ty,
                    ..
                }) => {
                    // FIXME: Maybe these calls to `ast_ty_to_ty` can be removed (and the ones below)
                    let ty = <dyn AstConv<'_>>::ast_ty_to_ty(self, bounded_ty);
                    Some((ty, bounds))
                }
                _ => None,
            })
            .map(|(ty, bounds)| match ty.kind() {
                ty::Param(param_ty) if param_ty == expected_ty_as_param => Ok(Some(bounds)),
                // check whether there is any predicate that contains our `T`, like `Option<T>: Send`
                _ => match ty.contains(expected) {
                    true => Err(()),
                    false => Ok(None),
                },
            })
            .collect::<Result<Vec<_>, _>>();

        let Ok(where_predicates) = where_predicates else { return };

        // now get all predicates in the same types as the where bounds, so we can chain them
        let predicates_from_where =
            where_predicates.iter().flatten().flat_map(|bounds| bounds.iter());

        // extract all bounds from the source code using their spans
        let all_matching_bounds_strs = predicates_from_where
            .filter_map(|bound| match bound {
                GenericBound::Trait(_, _) => {
                    self.tcx.sess.source_map().span_to_snippet(bound.span()).ok()
                }
                _ => None,
            })
            .collect::<Vec<String>>();

        if all_matching_bounds_strs.len() == 0 {
            return;
        }

        let all_bounds_str = all_matching_bounds_strs.join(" + ");

        let ty_param_used_in_fn_params = fn_parameters.iter().any(|param| {
                let ty = <dyn AstConv<'_>>::ast_ty_to_ty(self, param);
                matches!(ty.kind(), ty::Param(fn_param_ty_param) if expected_ty_as_param == fn_param_ty_param)
            });

        if ty_param_used_in_fn_params {
            return;
        }

        err.span_suggestion(
            fn_return.span(),
            "consider using an impl return type",
            format!("impl {}", all_bounds_str),
            Applicability::MaybeIncorrect,
        );
    }

    pub(in super::super) fn suggest_missing_break_or_return_expr(
        &self,
        err: &mut Diagnostic,
        expr: &'tcx hir::Expr<'tcx>,
        fn_decl: &hir::FnDecl<'_>,
        expected: Ty<'tcx>,
        found: Ty<'tcx>,
        id: hir::HirId,
        fn_id: hir::HirId,
    ) {
        if !expected.is_unit() {
            return;
        }
        let found = self.resolve_vars_with_obligations(found);

        let in_loop = self.is_loop(id)
            || self.tcx.hir().parent_iter(id).any(|(parent_id, _)| self.is_loop(parent_id));

        let in_local_statement = self.is_local_statement(id)
            || self
                .tcx
                .hir()
                .parent_iter(id)
                .any(|(parent_id, _)| self.is_local_statement(parent_id));

        if in_loop && in_local_statement {
            err.multipart_suggestion(
                "you might have meant to break the loop with this value",
                vec![
                    (expr.span.shrink_to_lo(), "break ".to_string()),
                    (expr.span.shrink_to_hi(), ";".to_string()),
                ],
                Applicability::MaybeIncorrect,
            );
            return;
        }

        if let hir::FnRetTy::Return(ty) = fn_decl.output {
            let ty = <dyn AstConv<'_>>::ast_ty_to_ty(self, ty);
            let bound_vars = self.tcx.late_bound_vars(fn_id);
            let ty = self.tcx.erase_late_bound_regions(Binder::bind_with_vars(ty, bound_vars));
            let ty = self.normalize_associated_types_in(expr.span, ty);
            let ty = match self.tcx.asyncness(fn_id.owner) {
                hir::IsAsync::Async => {
                    let infcx = self.tcx.infer_ctxt().build();
                    infcx
                        .get_impl_future_output_ty(ty)
                        .unwrap_or_else(|| {
                            span_bug!(
                                fn_decl.output.span(),
                                "failed to get output type of async function"
                            )
                        })
                        .skip_binder()
                }
                hir::IsAsync::NotAsync => ty,
            };
            if self.can_coerce(found, ty) {
                err.multipart_suggestion(
                    "you might have meant to return this value",
                    vec![
                        (expr.span.shrink_to_lo(), "return ".to_string()),
                        (expr.span.shrink_to_hi(), ";".to_string()),
                    ],
                    Applicability::MaybeIncorrect,
                );
            }
        }
    }

    pub(in super::super) fn suggest_missing_parentheses(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'_>,
    ) -> bool {
        let sp = self.tcx.sess.source_map().start_point(expr.span);
        if let Some(sp) = self.tcx.sess.parse_sess.ambiguous_block_expr_parse.borrow().get(&sp) {
            // `{ 42 } &&x` (#61475) or `{ 42 } && if x { 1 } else { 0 }`
            err.subdiagnostic(ExprParenthesesNeeded::surrounding(*sp));
            true
        } else {
            false
        }
    }

    /// Given an expression type mismatch, peel any `&` expressions until we get to
    /// a block expression, and then suggest replacing the braces with square braces
    /// if it was possibly mistaken array syntax.
    pub(crate) fn suggest_block_to_brackets_peeling_refs(
        &self,
        diag: &mut Diagnostic,
        mut expr: &hir::Expr<'_>,
        mut expr_ty: Ty<'tcx>,
        mut expected_ty: Ty<'tcx>,
    ) -> bool {
        loop {
            match (&expr.kind, expr_ty.kind(), expected_ty.kind()) {
                (
                    hir::ExprKind::AddrOf(_, _, inner_expr),
                    ty::Ref(_, inner_expr_ty, _),
                    ty::Ref(_, inner_expected_ty, _),
                ) => {
                    expr = *inner_expr;
                    expr_ty = *inner_expr_ty;
                    expected_ty = *inner_expected_ty;
                }
                (hir::ExprKind::Block(blk, _), _, _) => {
                    self.suggest_block_to_brackets(diag, *blk, expr_ty, expected_ty);
                    break true;
                }
                _ => break false,
            }
        }
    }

    pub(crate) fn suggest_copied_or_cloned(
        &self,
        diag: &mut Diagnostic,
        expr: &hir::Expr<'_>,
        expr_ty: Ty<'tcx>,
        expected_ty: Ty<'tcx>,
    ) -> bool {
        let ty::Adt(adt_def, substs) = expr_ty.kind() else { return false; };
        let ty::Adt(expected_adt_def, expected_substs) = expected_ty.kind() else { return false; };
        if adt_def != expected_adt_def {
            return false;
        }

        let mut suggest_copied_or_cloned = || {
            let expr_inner_ty = substs.type_at(0);
            let expected_inner_ty = expected_substs.type_at(0);
            if let ty::Ref(_, ty, hir::Mutability::Not) = expr_inner_ty.kind()
                && self.can_eq(self.param_env, *ty, expected_inner_ty).is_ok()
            {
                let def_path = self.tcx.def_path_str(adt_def.did());
                if self.type_is_copy_modulo_regions(self.param_env, *ty, expr.span) {
                    diag.span_suggestion_verbose(
                        expr.span.shrink_to_hi(),
                        format!(
                            "use `{def_path}::copied` to copy the value inside the `{def_path}`"
                        ),
                        ".copied()",
                        Applicability::MachineApplicable,
                    );
                    return true;
                } else if let Some(clone_did) = self.tcx.lang_items().clone_trait()
                    && rustc_trait_selection::traits::type_known_to_meet_bound_modulo_regions(
                        self,
                        self.param_env,
                        *ty,
                        clone_did,
                        expr.span
                    )
                {
                    diag.span_suggestion_verbose(
                        expr.span.shrink_to_hi(),
                        format!(
                            "use `{def_path}::cloned` to clone the value inside the `{def_path}`"
                        ),
                        ".cloned()",
                        Applicability::MachineApplicable,
                    );
                    return true;
                }
            }
            false
        };

        if let Some(result_did) = self.tcx.get_diagnostic_item(sym::Result)
            && adt_def.did() == result_did
            // Check that the error types are equal
            && self.can_eq(self.param_env, substs.type_at(1), expected_substs.type_at(1)).is_ok()
        {
            return suggest_copied_or_cloned();
        } else if let Some(option_did) = self.tcx.get_diagnostic_item(sym::Option)
            && adt_def.did() == option_did
        {
            return suggest_copied_or_cloned();
        }

        false
    }

    pub(crate) fn suggest_into(
        &self,
        diag: &mut Diagnostic,
        expr: &hir::Expr<'_>,
        expr_ty: Ty<'tcx>,
        expected_ty: Ty<'tcx>,
    ) -> bool {
        let expr = expr.peel_blocks();

        // We have better suggestions for scalar interconversions...
        if expr_ty.is_scalar() && expected_ty.is_scalar() {
            return false;
        }

        // Don't suggest turning a block into another type (e.g. `{}.into()`)
        if matches!(expr.kind, hir::ExprKind::Block(..)) {
            return false;
        }

        // We'll later suggest `.as_ref` when noting the type error,
        // so skip if we will suggest that instead.
        if self.err_ctxt().should_suggest_as_ref(expected_ty, expr_ty).is_some() {
            return false;
        }

        if let Some(into_def_id) = self.tcx.get_diagnostic_item(sym::Into)
            && self.predicate_must_hold_modulo_regions(&traits::Obligation::new(
                self.misc(expr.span),
                self.param_env,
                ty::Binder::dummy(ty::TraitRef {
                    def_id: into_def_id,
                    substs: self.tcx.mk_substs_trait(expr_ty, &[expected_ty.into()]),
                })
                .to_poly_trait_predicate()
                .to_predicate(self.tcx),
            ))
        {
            let sugg = if expr.precedence().order() >= PREC_POSTFIX {
                vec![(expr.span.shrink_to_hi(), ".into()".to_owned())]
            } else {
                vec![(expr.span.shrink_to_lo(), "(".to_owned()), (expr.span.shrink_to_hi(), ").into()".to_owned())]
            };
            diag.multipart_suggestion(
                format!("call `Into::into` on this expression to convert `{expr_ty}` into `{expected_ty}`"),
                sugg,
                Applicability::MaybeIncorrect
            );
            return true;
        }

        false
    }

    /// Suggest wrapping the block in square brackets instead of curly braces
    /// in case the block was mistaken array syntax, e.g. `{ 1 }` -> `[ 1 ]`.
    pub(crate) fn suggest_block_to_brackets(
        &self,
        diag: &mut Diagnostic,
        blk: &hir::Block<'_>,
        blk_ty: Ty<'tcx>,
        expected_ty: Ty<'tcx>,
    ) {
        if let ty::Slice(elem_ty) | ty::Array(elem_ty, _) = expected_ty.kind() {
            if self.can_coerce(blk_ty, *elem_ty)
                && blk.stmts.is_empty()
                && blk.rules == hir::BlockCheckMode::DefaultBlock
            {
                let source_map = self.tcx.sess.source_map();
                if let Ok(snippet) = source_map.span_to_snippet(blk.span) {
                    if snippet.starts_with('{') && snippet.ends_with('}') {
                        diag.multipart_suggestion_verbose(
                            "to create an array, use square brackets instead of curly braces",
                            vec![
                                (
                                    blk.span
                                        .shrink_to_lo()
                                        .with_hi(rustc_span::BytePos(blk.span.lo().0 + 1)),
                                    "[".to_string(),
                                ),
                                (
                                    blk.span
                                        .shrink_to_hi()
                                        .with_lo(rustc_span::BytePos(blk.span.hi().0 - 1)),
                                    "]".to_string(),
                                ),
                            ],
                            Applicability::MachineApplicable,
                        );
                    }
                }
            }
        }
    }

    fn is_loop(&self, id: hir::HirId) -> bool {
        let node = self.tcx.hir().get(id);
        matches!(node, Node::Expr(Expr { kind: ExprKind::Loop(..), .. }))
    }

    fn is_local_statement(&self, id: hir::HirId) -> bool {
        let node = self.tcx.hir().get(id);
        matches!(node, Node::Stmt(Stmt { kind: StmtKind::Local(..), .. }))
    }

    /// Suggest that `&T` was cloned instead of `T` because `T` does not implement `Clone`,
    /// which is a side-effect of autoref.
    pub(crate) fn note_type_is_not_clone(
        &self,
        diag: &mut Diagnostic,
        expected_ty: Ty<'tcx>,
        found_ty: Ty<'tcx>,
        expr: &hir::Expr<'_>,
    ) {
        let hir::ExprKind::MethodCall(segment, callee_expr, &[], _) = expr.kind else { return; };
        let Some(clone_trait_did) = self.tcx.lang_items().clone_trait() else { return; };
        let ty::Ref(_, pointee_ty, _) = found_ty.kind() else { return };
        let results = self.typeck_results.borrow();
        // First, look for a `Clone::clone` call
        if segment.ident.name == sym::clone
            && results.type_dependent_def_id(expr.hir_id).map_or(
                false,
                |did| {
                    let assoc_item = self.tcx.associated_item(did);
                    assoc_item.container == ty::AssocItemContainer::TraitContainer
                        && assoc_item.container_id(self.tcx) == clone_trait_did
                },
            )
            // If that clone call hasn't already dereferenced the self type (i.e. don't give this
            // diagnostic in cases where we have `(&&T).clone()` and we expect `T`).
            && !results.expr_adjustments(callee_expr).iter().any(|adj| matches!(adj.kind, ty::adjustment::Adjust::Deref(..)))
            // Check that we're in fact trying to clone into the expected type
            && self.can_coerce(*pointee_ty, expected_ty)
            // And the expected type doesn't implement `Clone`
            && !self.predicate_must_hold_considering_regions(&traits::Obligation {
                cause: traits::ObligationCause::dummy(),
                param_env: self.param_env,
                recursion_depth: 0,
                predicate: ty::Binder::dummy(ty::TraitRef {
                    def_id: clone_trait_did,
                    substs: self.tcx.mk_substs([expected_ty.into()].iter()),
                })
                .without_const()
                .to_predicate(self.tcx),
            })
        {
            diag.span_note(
                callee_expr.span,
                &format!(
                    "`{expected_ty}` does not implement `Clone`, so `{found_ty}` was cloned instead"
                ),
            );
        }
    }

    /// A common error is to add an extra semicolon:
    ///
    /// ```compile_fail,E0308
    /// fn foo() -> usize {
    ///     22;
    /// }
    /// ```
    ///
    /// This routine checks if the final statement in a block is an
    /// expression with an explicit semicolon whose type is compatible
    /// with `expected_ty`. If so, it suggests removing the semicolon.
    pub(crate) fn consider_removing_semicolon(
        &self,
        blk: &'tcx hir::Block<'tcx>,
        expected_ty: Ty<'tcx>,
        err: &mut Diagnostic,
    ) -> bool {
        if let Some((span_semi, boxed)) = self.err_ctxt().could_remove_semicolon(blk, expected_ty) {
            if let StatementAsExpression::NeedsBoxing = boxed {
                err.span_suggestion_verbose(
                    span_semi,
                    "consider removing this semicolon and boxing the expression",
                    "",
                    Applicability::HasPlaceholders,
                );
            } else {
                err.span_suggestion_short(
                    span_semi,
                    "remove this semicolon to return this value",
                    "",
                    Applicability::MachineApplicable,
                );
            }
            true
        } else {
            false
        }
    }
}
