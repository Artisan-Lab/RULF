use crate::FnCtxt;
use rustc_ast::util::parser::PREC_POSTFIX;
use rustc_errors::{Applicability, Diagnostic, DiagnosticBuilder, ErrorGuaranteed};
use rustc_hir as hir;
use rustc_hir::lang_items::LangItem;
use rustc_hir::{is_range_literal, Node};
use rustc_infer::infer::InferOk;
use rustc_middle::lint::in_external_macro;
use rustc_middle::middle::stability::EvalResult;
use rustc_middle::ty::adjustment::AllowTwoPhase;
use rustc_middle::ty::error::{ExpectedFound, TypeError};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, Article, AssocItem, Ty, TypeAndMut};
use rustc_span::symbol::{sym, Symbol};
use rustc_span::{BytePos, Span};
use rustc_trait_selection::infer::InferCtxtExt as _;
use rustc_trait_selection::traits::ObligationCause;

use super::method::probe;

use std::iter;

impl<'a, 'tcx> FnCtxt<'a, 'tcx> {
    pub fn emit_coerce_suggestions(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'tcx>,
        expr_ty: Ty<'tcx>,
        expected: Ty<'tcx>,
        expected_ty_expr: Option<&'tcx hir::Expr<'tcx>>,
        error: Option<TypeError<'tcx>>,
    ) {
        self.annotate_expected_due_to_let_ty(err, expr, error);

        // Use `||` to give these suggestions a precedence
        let _ = self.suggest_missing_parentheses(err, expr)
            || self.suggest_deref_ref_or_into(err, expr, expected, expr_ty, expected_ty_expr)
            || self.suggest_compatible_variants(err, expr, expected, expr_ty)
            || self.suggest_non_zero_new_unwrap(err, expr, expected, expr_ty)
            || self.suggest_calling_boxed_future_when_appropriate(err, expr, expected, expr_ty)
            || self.suggest_no_capture_closure(err, expected, expr_ty)
            || self.suggest_boxing_when_appropriate(err, expr, expected, expr_ty)
            || self.suggest_block_to_brackets_peeling_refs(err, expr, expr_ty, expected)
            || self.suggest_copied_or_cloned(err, expr, expr_ty, expected)
            || self.suggest_into(err, expr, expr_ty, expected);

        self.note_type_is_not_clone(err, expected, expr_ty, expr);
        self.note_need_for_fn_pointer(err, expected, expr_ty);
        self.note_internal_mutation_in_method(err, expr, expected, expr_ty);
    }

    // Requires that the two types unify, and prints an error message if
    // they don't.
    pub fn demand_suptype(&self, sp: Span, expected: Ty<'tcx>, actual: Ty<'tcx>) {
        if let Some(mut e) = self.demand_suptype_diag(sp, expected, actual) {
            e.emit();
        }
    }

    pub fn demand_suptype_diag(
        &self,
        sp: Span,
        expected: Ty<'tcx>,
        actual: Ty<'tcx>,
    ) -> Option<DiagnosticBuilder<'tcx, ErrorGuaranteed>> {
        self.demand_suptype_with_origin(&self.misc(sp), expected, actual)
    }

    #[instrument(skip(self), level = "debug")]
    pub fn demand_suptype_with_origin(
        &self,
        cause: &ObligationCause<'tcx>,
        expected: Ty<'tcx>,
        actual: Ty<'tcx>,
    ) -> Option<DiagnosticBuilder<'tcx, ErrorGuaranteed>> {
        match self.at(cause, self.param_env).sup(expected, actual) {
            Ok(InferOk { obligations, value: () }) => {
                self.register_predicates(obligations);
                None
            }
            Err(e) => Some(self.err_ctxt().report_mismatched_types(&cause, expected, actual, e)),
        }
    }

    pub fn demand_eqtype(&self, sp: Span, expected: Ty<'tcx>, actual: Ty<'tcx>) {
        if let Some(mut err) = self.demand_eqtype_diag(sp, expected, actual) {
            err.emit();
        }
    }

    pub fn demand_eqtype_diag(
        &self,
        sp: Span,
        expected: Ty<'tcx>,
        actual: Ty<'tcx>,
    ) -> Option<DiagnosticBuilder<'tcx, ErrorGuaranteed>> {
        self.demand_eqtype_with_origin(&self.misc(sp), expected, actual)
    }

    pub fn demand_eqtype_with_origin(
        &self,
        cause: &ObligationCause<'tcx>,
        expected: Ty<'tcx>,
        actual: Ty<'tcx>,
    ) -> Option<DiagnosticBuilder<'tcx, ErrorGuaranteed>> {
        match self.at(cause, self.param_env).eq(expected, actual) {
            Ok(InferOk { obligations, value: () }) => {
                self.register_predicates(obligations);
                None
            }
            Err(e) => Some(self.err_ctxt().report_mismatched_types(cause, expected, actual, e)),
        }
    }

    pub fn demand_coerce(
        &self,
        expr: &hir::Expr<'tcx>,
        checked_ty: Ty<'tcx>,
        expected: Ty<'tcx>,
        expected_ty_expr: Option<&'tcx hir::Expr<'tcx>>,
        allow_two_phase: AllowTwoPhase,
    ) -> Ty<'tcx> {
        let (ty, err) =
            self.demand_coerce_diag(expr, checked_ty, expected, expected_ty_expr, allow_two_phase);
        if let Some(mut err) = err {
            err.emit();
        }
        ty
    }

    /// Checks that the type of `expr` can be coerced to `expected`.
    ///
    /// N.B., this code relies on `self.diverges` to be accurate. In particular, assignments to `!`
    /// will be permitted if the diverges flag is currently "always".
    #[instrument(level = "debug", skip(self, expr, expected_ty_expr, allow_two_phase))]
    pub fn demand_coerce_diag(
        &self,
        expr: &hir::Expr<'tcx>,
        checked_ty: Ty<'tcx>,
        expected: Ty<'tcx>,
        expected_ty_expr: Option<&'tcx hir::Expr<'tcx>>,
        allow_two_phase: AllowTwoPhase,
    ) -> (Ty<'tcx>, Option<DiagnosticBuilder<'tcx, ErrorGuaranteed>>) {
        let expected = self.resolve_vars_with_obligations(expected);

        let e = match self.try_coerce(expr, checked_ty, expected, allow_two_phase, None) {
            Ok(ty) => return (ty, None),
            Err(e) => e,
        };

        self.set_tainted_by_errors();
        let expr = expr.peel_drop_temps();
        let cause = self.misc(expr.span);
        let expr_ty = self.resolve_vars_with_obligations(checked_ty);
        let mut err = self.err_ctxt().report_mismatched_types(&cause, expected, expr_ty, e.clone());

        let is_insufficiently_polymorphic =
            matches!(e, TypeError::RegionsInsufficientlyPolymorphic(..));

        // FIXME(#73154): For now, we do leak check when coercing function
        // pointers in typeck, instead of only during borrowck. This can lead
        // to these `RegionsInsufficientlyPolymorphic` errors that aren't helpful.
        if !is_insufficiently_polymorphic {
            self.emit_coerce_suggestions(
                &mut err,
                expr,
                expr_ty,
                expected,
                expected_ty_expr,
                Some(e),
            );
        }

        (expected, Some(err))
    }

    fn annotate_expected_due_to_let_ty(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'_>,
        error: Option<TypeError<'_>>,
    ) {
        let parent = self.tcx.hir().get_parent_node(expr.hir_id);
        match (self.tcx.hir().find(parent), error) {
            (Some(hir::Node::Local(hir::Local { ty: Some(ty), init: Some(init), .. })), _)
                if init.hir_id == expr.hir_id =>
            {
                // Point at `let` assignment type.
                err.span_label(ty.span, "expected due to this");
            }
            (
                Some(hir::Node::Expr(hir::Expr {
                    kind: hir::ExprKind::Assign(lhs, rhs, _), ..
                })),
                Some(TypeError::Sorts(ExpectedFound { expected, .. })),
            ) if rhs.hir_id == expr.hir_id && !expected.is_closure() => {
                // We ignore closures explicitly because we already point at them elsewhere.
                // Point at the assigned-to binding.
                let mut primary_span = lhs.span;
                let mut secondary_span = lhs.span;
                let mut post_message = "";
                match lhs.kind {
                    hir::ExprKind::Path(hir::QPath::Resolved(
                        None,
                        hir::Path {
                            res:
                                hir::def::Res::Def(
                                    hir::def::DefKind::Static(_) | hir::def::DefKind::Const,
                                    def_id,
                                ),
                            ..
                        },
                    )) => {
                        if let Some(hir::Node::Item(hir::Item {
                            ident,
                            kind: hir::ItemKind::Static(ty, ..) | hir::ItemKind::Const(ty, ..),
                            ..
                        })) = self.tcx.hir().get_if_local(*def_id)
                        {
                            primary_span = ty.span;
                            secondary_span = ident.span;
                            post_message = " type";
                        }
                    }
                    hir::ExprKind::Path(hir::QPath::Resolved(
                        None,
                        hir::Path { res: hir::def::Res::Local(hir_id), .. },
                    )) => {
                        if let Some(hir::Node::Pat(pat)) = self.tcx.hir().find(*hir_id) {
                            let parent = self.tcx.hir().get_parent_node(pat.hir_id);
                            primary_span = pat.span;
                            secondary_span = pat.span;
                            match self.tcx.hir().find(parent) {
                                Some(hir::Node::Local(hir::Local { ty: Some(ty), .. })) => {
                                    primary_span = ty.span;
                                    post_message = " type";
                                }
                                Some(hir::Node::Local(hir::Local { init: Some(init), .. })) => {
                                    primary_span = init.span;
                                    post_message = " value";
                                }
                                Some(hir::Node::Param(hir::Param { ty_span, .. })) => {
                                    primary_span = *ty_span;
                                    post_message = " parameter type";
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }

                if primary_span != secondary_span
                    && self
                        .tcx
                        .sess
                        .source_map()
                        .is_multiline(secondary_span.shrink_to_hi().until(primary_span))
                {
                    // We are pointing at the binding's type or initializer value, but it's pattern
                    // is in a different line, so we point at both.
                    err.span_label(secondary_span, "expected due to the type of this binding");
                    err.span_label(primary_span, &format!("expected due to this{post_message}"));
                } else if post_message == "" {
                    // We are pointing at either the assignment lhs or the binding def pattern.
                    err.span_label(primary_span, "expected due to the type of this binding");
                } else {
                    // We are pointing at the binding's type or initializer value.
                    err.span_label(primary_span, &format!("expected due to this{post_message}"));
                }

                if !lhs.is_syntactic_place_expr() {
                    // We already emitted E0070 "invalid left-hand side of assignment", so we
                    // silence this.
                    err.downgrade_to_delayed_bug();
                }
            }
            _ => {}
        }
    }

    /// If the expected type is an enum (Issue #55250) with any variants whose
    /// sole field is of the found type, suggest such variants. (Issue #42764)
    fn suggest_compatible_variants(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'_>,
        expected: Ty<'tcx>,
        expr_ty: Ty<'tcx>,
    ) -> bool {
        if let ty::Adt(expected_adt, substs) = expected.kind() {
            if let hir::ExprKind::Field(base, ident) = expr.kind {
                let base_ty = self.typeck_results.borrow().expr_ty(base);
                if self.can_eq(self.param_env, base_ty, expected).is_ok()
                    && let Some(base_span) = base.span.find_ancestor_inside(expr.span)
                {
                    err.span_suggestion_verbose(
                        expr.span.with_lo(base_span.hi()),
                        format!("consider removing the tuple struct field `{ident}`"),
                        "",
                        Applicability::MaybeIncorrect,
                    );
                    return true;
                }
            }

            // If the expression is of type () and it's the return expression of a block,
            // we suggest adding a separate return expression instead.
            // (To avoid things like suggesting `Ok(while .. { .. })`.)
            if expr_ty.is_unit() {
                let mut id = expr.hir_id;
                let mut parent;

                // Unroll desugaring, to make sure this works for `for` loops etc.
                loop {
                    parent = self.tcx.hir().get_parent_node(id);
                    if let Some(parent_span) = self.tcx.hir().opt_span(parent) {
                        if parent_span.find_ancestor_inside(expr.span).is_some() {
                            // The parent node is part of the same span, so is the result of the
                            // same expansion/desugaring and not the 'real' parent node.
                            id = parent;
                            continue;
                        }
                    }
                    break;
                }

                if let Some(hir::Node::Block(&hir::Block {
                    span: block_span, expr: Some(e), ..
                })) = self.tcx.hir().find(parent)
                {
                    if e.hir_id == id {
                        if let Some(span) = expr.span.find_ancestor_inside(block_span) {
                            let return_suggestions = if self
                                .tcx
                                .is_diagnostic_item(sym::Result, expected_adt.did())
                            {
                                vec!["Ok(())"]
                            } else if self.tcx.is_diagnostic_item(sym::Option, expected_adt.did()) {
                                vec!["None", "Some(())"]
                            } else {
                                return false;
                            };
                            if let Some(indent) =
                                self.tcx.sess.source_map().indentation_before(span.shrink_to_lo())
                            {
                                // Add a semicolon, except after `}`.
                                let semicolon =
                                    match self.tcx.sess.source_map().span_to_snippet(span) {
                                        Ok(s) if s.ends_with('}') => "",
                                        _ => ";",
                                    };
                                err.span_suggestions(
                                    span.shrink_to_hi(),
                                    "try adding an expression at the end of the block",
                                    return_suggestions
                                        .into_iter()
                                        .map(|r| format!("{semicolon}\n{indent}{r}")),
                                    Applicability::MaybeIncorrect,
                                );
                            }
                            return true;
                        }
                    }
                }
            }

            let compatible_variants: Vec<(String, _, _, Option<String>)> = expected_adt
                .variants()
                .iter()
                .filter(|variant| {
                    variant.fields.len() == 1
                })
                .filter_map(|variant| {
                    let sole_field = &variant.fields[0];

                    let field_is_local = sole_field.did.is_local();
                    let field_is_accessible =
                        sole_field.vis.is_accessible_from(expr.hir_id.owner.def_id, self.tcx)
                        // Skip suggestions for unstable public fields (for example `Pin::pointer`)
                        && matches!(self.tcx.eval_stability(sole_field.did, None, expr.span, None), EvalResult::Allow | EvalResult::Unmarked);

                    if !field_is_local && !field_is_accessible {
                        return None;
                    }

                    let note_about_variant_field_privacy = (field_is_local && !field_is_accessible)
                        .then(|| format!(" (its field is private, but it's local to this crate and its privacy can be changed)"));

                    let sole_field_ty = sole_field.ty(self.tcx, substs);
                    if self.can_coerce(expr_ty, sole_field_ty) {
                        let variant_path =
                            with_no_trimmed_paths!(self.tcx.def_path_str(variant.def_id));
                        // FIXME #56861: DRYer prelude filtering
                        if let Some(path) = variant_path.strip_prefix("std::prelude::")
                            && let Some((_, path)) = path.split_once("::")
                        {
                            return Some((path.to_string(), variant.ctor_kind, sole_field.name, note_about_variant_field_privacy));
                        }
                        Some((variant_path, variant.ctor_kind, sole_field.name, note_about_variant_field_privacy))
                    } else {
                        None
                    }
                })
                .collect();

            let suggestions_for = |variant: &_, ctor, field_name| {
                let prefix = match self.maybe_get_struct_pattern_shorthand_field(expr) {
                    Some(ident) => format!("{ident}: "),
                    None => String::new(),
                };

                let (open, close) = match ctor {
                    hir::def::CtorKind::Fn => ("(".to_owned(), ")"),
                    hir::def::CtorKind::Fictive => (format!(" {{ {field_name}: "), " }"),

                    // unit variants don't have fields
                    hir::def::CtorKind::Const => unreachable!(),
                };

                // Suggest constructor as deep into the block tree as possible.
                // This fixes https://github.com/rust-lang/rust/issues/101065,
                // and also just helps make the most minimal suggestions.
                let mut expr = expr;
                while let hir::ExprKind::Block(block, _) = &expr.kind
                    && let Some(expr_) = &block.expr
                {
                    expr = expr_
                }

                vec![
                    (expr.span.shrink_to_lo(), format!("{prefix}{variant}{open}")),
                    (expr.span.shrink_to_hi(), close.to_owned()),
                ]
            };

            match &compatible_variants[..] {
                [] => { /* No variants to format */ }
                [(variant, ctor_kind, field_name, note)] => {
                    // Just a single matching variant.
                    err.multipart_suggestion_verbose(
                        &format!(
                            "try wrapping the expression in `{variant}`{note}",
                            note = note.as_deref().unwrap_or("")
                        ),
                        suggestions_for(&**variant, *ctor_kind, *field_name),
                        Applicability::MaybeIncorrect,
                    );
                    return true;
                }
                _ => {
                    // More than one matching variant.
                    err.multipart_suggestions(
                        &format!(
                            "try wrapping the expression in a variant of `{}`",
                            self.tcx.def_path_str(expected_adt.did())
                        ),
                        compatible_variants.into_iter().map(
                            |(variant, ctor_kind, field_name, _)| {
                                suggestions_for(&variant, ctor_kind, field_name)
                            },
                        ),
                        Applicability::MaybeIncorrect,
                    );
                    return true;
                }
            }
        }

        false
    }

    fn suggest_non_zero_new_unwrap(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'_>,
        expected: Ty<'tcx>,
        expr_ty: Ty<'tcx>,
    ) -> bool {
        let tcx = self.tcx;
        let (adt, unwrap) = match expected.kind() {
            // In case Option<NonZero*> is wanted, but * is provided, suggest calling new
            ty::Adt(adt, substs) if tcx.is_diagnostic_item(sym::Option, adt.did()) => {
                // Unwrap option
                let ty::Adt(adt, _) = substs.type_at(0).kind() else { return false; };

                (adt, "")
            }
            // In case NonZero* is wanted, but * is provided also add `.unwrap()` to satisfy types
            ty::Adt(adt, _) => (adt, ".unwrap()"),
            _ => return false,
        };

        let map = [
            (sym::NonZeroU8, tcx.types.u8),
            (sym::NonZeroU16, tcx.types.u16),
            (sym::NonZeroU32, tcx.types.u32),
            (sym::NonZeroU64, tcx.types.u64),
            (sym::NonZeroU128, tcx.types.u128),
            (sym::NonZeroI8, tcx.types.i8),
            (sym::NonZeroI16, tcx.types.i16),
            (sym::NonZeroI32, tcx.types.i32),
            (sym::NonZeroI64, tcx.types.i64),
            (sym::NonZeroI128, tcx.types.i128),
        ];

        let Some((s, _)) = map
            .iter()
            .find(|&&(s, t)| self.tcx.is_diagnostic_item(s, adt.did()) && self.can_coerce(expr_ty, t))
            else { return false; };

        let path = self.tcx.def_path_str(adt.non_enum_variant().def_id);

        err.multipart_suggestion(
            format!("consider calling `{s}::new`"),
            vec![
                (expr.span.shrink_to_lo(), format!("{path}::new(")),
                (expr.span.shrink_to_hi(), format!("){unwrap}")),
            ],
            Applicability::MaybeIncorrect,
        );

        true
    }

    pub fn get_conversion_methods(
        &self,
        span: Span,
        expected: Ty<'tcx>,
        checked_ty: Ty<'tcx>,
        hir_id: hir::HirId,
    ) -> Vec<AssocItem> {
        let methods = self.probe_for_return_type(
            span,
            probe::Mode::MethodCall,
            expected,
            checked_ty,
            hir_id,
            |m| {
                self.has_only_self_parameter(m)
                    && self
                        .tcx
                        // This special internal attribute is used to permit
                        // "identity-like" conversion methods to be suggested here.
                        //
                        // FIXME (#46459 and #46460): ideally
                        // `std::convert::Into::into` and `std::borrow:ToOwned` would
                        // also be `#[rustc_conversion_suggestion]`, if not for
                        // method-probing false-positives and -negatives (respectively).
                        //
                        // FIXME? Other potential candidate methods: `as_ref` and
                        // `as_mut`?
                        .has_attr(m.def_id, sym::rustc_conversion_suggestion)
            },
        );

        methods
    }

    /// This function checks whether the method is not static and does not accept other parameters than `self`.
    fn has_only_self_parameter(&self, method: &AssocItem) -> bool {
        match method.kind {
            ty::AssocKind::Fn => {
                method.fn_has_self_parameter
                    && self.tcx.fn_sig(method.def_id).inputs().skip_binder().len() == 1
            }
            _ => false,
        }
    }

    /// Identify some cases where `as_ref()` would be appropriate and suggest it.
    ///
    /// Given the following code:
    /// ```compile_fail,E0308
    /// struct Foo;
    /// fn takes_ref(_: &Foo) {}
    /// let ref opt = Some(Foo);
    ///
    /// opt.map(|param| takes_ref(param));
    /// ```
    /// Suggest using `opt.as_ref().map(|param| takes_ref(param));` instead.
    ///
    /// It only checks for `Option` and `Result` and won't work with
    /// ```ignore (illustrative)
    /// opt.map(|param| { takes_ref(param) });
    /// ```
    fn can_use_as_ref(&self, expr: &hir::Expr<'_>) -> Option<(Span, &'static str, String)> {
        let hir::ExprKind::Path(hir::QPath::Resolved(_, ref path)) = expr.kind else {
            return None;
        };

        let hir::def::Res::Local(local_id) = path.res else {
            return None;
        };

        let local_parent = self.tcx.hir().get_parent_node(local_id);
        let Some(Node::Param(hir::Param { hir_id: param_hir_id, .. })) = self.tcx.hir().find(local_parent) else {
            return None;
        };

        let param_parent = self.tcx.hir().get_parent_node(*param_hir_id);
        let Some(Node::Expr(hir::Expr {
            hir_id: expr_hir_id,
            kind: hir::ExprKind::Closure(hir::Closure { fn_decl: closure_fn_decl, .. }),
            ..
        })) = self.tcx.hir().find(param_parent) else {
            return None;
        };

        let expr_parent = self.tcx.hir().get_parent_node(*expr_hir_id);
        let hir = self.tcx.hir().find(expr_parent);
        let closure_params_len = closure_fn_decl.inputs.len();
        let (
            Some(Node::Expr(hir::Expr {
                kind: hir::ExprKind::MethodCall(method_path, receiver, ..),
                ..
            })),
            1,
        ) = (hir, closure_params_len) else {
            return None;
        };

        let self_ty = self.typeck_results.borrow().expr_ty(receiver);
        let name = method_path.ident.name;
        let is_as_ref_able = match self_ty.peel_refs().kind() {
            ty::Adt(def, _) => {
                (self.tcx.is_diagnostic_item(sym::Option, def.did())
                    || self.tcx.is_diagnostic_item(sym::Result, def.did()))
                    && (name == sym::map || name == sym::and_then)
            }
            _ => false,
        };
        match (is_as_ref_able, self.sess().source_map().span_to_snippet(method_path.ident.span)) {
            (true, Ok(src)) => {
                let suggestion = format!("as_ref().{}", src);
                Some((method_path.ident.span, "consider using `as_ref` instead", suggestion))
            }
            _ => None,
        }
    }

    pub(crate) fn maybe_get_struct_pattern_shorthand_field(
        &self,
        expr: &hir::Expr<'_>,
    ) -> Option<Symbol> {
        let hir = self.tcx.hir();
        let local = match expr {
            hir::Expr {
                kind:
                    hir::ExprKind::Path(hir::QPath::Resolved(
                        None,
                        hir::Path {
                            res: hir::def::Res::Local(_),
                            segments: [hir::PathSegment { ident, .. }],
                            ..
                        },
                    )),
                ..
            } => Some(ident),
            _ => None,
        }?;

        match hir.find(hir.get_parent_node(expr.hir_id))? {
            Node::ExprField(field) => {
                if field.ident.name == local.name && field.is_shorthand {
                    return Some(local.name);
                }
            }
            _ => {}
        }

        None
    }

    /// If the given `HirId` corresponds to a block with a trailing expression, return that expression
    pub(crate) fn maybe_get_block_expr(
        &self,
        expr: &hir::Expr<'tcx>,
    ) -> Option<&'tcx hir::Expr<'tcx>> {
        match expr {
            hir::Expr { kind: hir::ExprKind::Block(block, ..), .. } => block.expr,
            _ => None,
        }
    }

    /// Returns whether the given expression is an `else if`.
    pub(crate) fn is_else_if_block(&self, expr: &hir::Expr<'_>) -> bool {
        if let hir::ExprKind::If(..) = expr.kind {
            let parent_id = self.tcx.hir().get_parent_node(expr.hir_id);
            if let Some(Node::Expr(hir::Expr {
                kind: hir::ExprKind::If(_, _, Some(else_expr)),
                ..
            })) = self.tcx.hir().find(parent_id)
            {
                return else_expr.hir_id == expr.hir_id;
            }
        }
        false
    }

    /// This function is used to determine potential "simple" improvements or users' errors and
    /// provide them useful help. For example:
    ///
    /// ```compile_fail,E0308
    /// fn some_fn(s: &str) {}
    ///
    /// let x = "hey!".to_owned();
    /// some_fn(x); // error
    /// ```
    ///
    /// No need to find every potential function which could make a coercion to transform a
    /// `String` into a `&str` since a `&` would do the trick!
    ///
    /// In addition of this check, it also checks between references mutability state. If the
    /// expected is mutable but the provided isn't, maybe we could just say "Hey, try with
    /// `&mut`!".
    pub fn check_ref(
        &self,
        expr: &hir::Expr<'tcx>,
        checked_ty: Ty<'tcx>,
        expected: Ty<'tcx>,
    ) -> Option<(
        Span,
        String,
        String,
        Applicability,
        bool, /* verbose */
        bool, /* suggest `&` or `&mut` type annotation */
    )> {
        let sess = self.sess();
        let sp = expr.span;

        // If the span is from an external macro, there's no suggestion we can make.
        if in_external_macro(sess, sp) {
            return None;
        }

        let sm = sess.source_map();

        let replace_prefix = |s: &str, old: &str, new: &str| {
            s.strip_prefix(old).map(|stripped| new.to_string() + stripped)
        };

        // `ExprKind::DropTemps` is semantically irrelevant for these suggestions.
        let expr = expr.peel_drop_temps();

        match (&expr.kind, expected.kind(), checked_ty.kind()) {
            (_, &ty::Ref(_, exp, _), &ty::Ref(_, check, _)) => match (exp.kind(), check.kind()) {
                (&ty::Str, &ty::Array(arr, _) | &ty::Slice(arr)) if arr == self.tcx.types.u8 => {
                    if let hir::ExprKind::Lit(_) = expr.kind
                        && let Ok(src) = sm.span_to_snippet(sp)
                        && replace_prefix(&src, "b\"", "\"").is_some()
                    {
                                let pos = sp.lo() + BytePos(1);
                                return Some((
                                    sp.with_hi(pos),
                                    "consider removing the leading `b`".to_string(),
                                    String::new(),
                                    Applicability::MachineApplicable,
                                    true,
                                    false,
                                ));
                            }
                        }
                (&ty::Array(arr, _) | &ty::Slice(arr), &ty::Str) if arr == self.tcx.types.u8 => {
                    if let hir::ExprKind::Lit(_) = expr.kind
                        && let Ok(src) = sm.span_to_snippet(sp)
                        && replace_prefix(&src, "\"", "b\"").is_some()
                    {
                                return Some((
                                    sp.shrink_to_lo(),
                                    "consider adding a leading `b`".to_string(),
                                    "b".to_string(),
                                    Applicability::MachineApplicable,
                                    true,
                                    false,
                                ));
                    }
                }
                _ => {}
            },
            (_, &ty::Ref(_, _, mutability), _) => {
                // Check if it can work when put into a ref. For example:
                //
                // ```
                // fn bar(x: &mut i32) {}
                //
                // let x = 0u32;
                // bar(&x); // error, expected &mut
                // ```
                let ref_ty = match mutability {
                    hir::Mutability::Mut => {
                        self.tcx.mk_mut_ref(self.tcx.mk_region(ty::ReStatic), checked_ty)
                    }
                    hir::Mutability::Not => {
                        self.tcx.mk_imm_ref(self.tcx.mk_region(ty::ReStatic), checked_ty)
                    }
                };
                if self.can_coerce(ref_ty, expected) {
                    let mut sugg_sp = sp;
                    if let hir::ExprKind::MethodCall(ref segment, receiver, args, _) = expr.kind {
                        let clone_trait =
                            self.tcx.require_lang_item(LangItem::Clone, Some(segment.ident.span));
                        if args.is_empty()
                            && self.typeck_results.borrow().type_dependent_def_id(expr.hir_id).map(
                                |did| {
                                    let ai = self.tcx.associated_item(did);
                                    ai.trait_container(self.tcx) == Some(clone_trait)
                                },
                            ) == Some(true)
                            && segment.ident.name == sym::clone
                        {
                            // If this expression had a clone call when suggesting borrowing
                            // we want to suggest removing it because it'd now be unnecessary.
                            sugg_sp = receiver.span;
                        }
                    }
                    if let Ok(src) = sm.span_to_snippet(sugg_sp) {
                        let needs_parens = match expr.kind {
                            // parenthesize if needed (Issue #46756)
                            hir::ExprKind::Cast(_, _) | hir::ExprKind::Binary(_, _, _) => true,
                            // parenthesize borrows of range literals (Issue #54505)
                            _ if is_range_literal(expr) => true,
                            _ => false,
                        };

                        if let Some(sugg) = self.can_use_as_ref(expr) {
                            return Some((
                                sugg.0,
                                sugg.1.to_string(),
                                sugg.2,
                                Applicability::MachineApplicable,
                                false,
                                false,
                            ));
                        }

                        let prefix = match self.maybe_get_struct_pattern_shorthand_field(expr) {
                            Some(ident) => format!("{ident}: "),
                            None => String::new(),
                        };

                        if let Some(hir::Node::Expr(hir::Expr {
                            kind: hir::ExprKind::Assign(..),
                            ..
                        })) = self.tcx.hir().find(self.tcx.hir().get_parent_node(expr.hir_id))
                        {
                            if mutability == hir::Mutability::Mut {
                                // Suppressing this diagnostic, we'll properly print it in `check_expr_assign`
                                return None;
                            }
                        }

                        let sugg_expr = if needs_parens { format!("({src})") } else { src };
                        return Some(match mutability {
                            hir::Mutability::Mut => (
                                sp,
                                "consider mutably borrowing here".to_string(),
                                format!("{prefix}&mut {sugg_expr}"),
                                Applicability::MachineApplicable,
                                false,
                                false,
                            ),
                            hir::Mutability::Not => (
                                sp,
                                "consider borrowing here".to_string(),
                                format!("{prefix}&{sugg_expr}"),
                                Applicability::MachineApplicable,
                                false,
                                false,
                            ),
                        });
                    }
                }
            }
            (
                hir::ExprKind::AddrOf(hir::BorrowKind::Ref, _, ref expr),
                _,
                &ty::Ref(_, checked, _),
            ) if self.can_sub(self.param_env, checked, expected).is_ok() => {
                // We have `&T`, check if what was expected was `T`. If so,
                // we may want to suggest removing a `&`.
                if sm.is_imported(expr.span) {
                    // Go through the spans from which this span was expanded,
                    // and find the one that's pointing inside `sp`.
                    //
                    // E.g. for `&format!("")`, where we want the span to the
                    // `format!()` invocation instead of its expansion.
                    if let Some(call_span) =
                        iter::successors(Some(expr.span), |s| s.parent_callsite())
                            .find(|&s| sp.contains(s))
                        && sm.is_span_accessible(call_span)
                    {
                        return Some((
                            sp.with_hi(call_span.lo()),
                            "consider removing the borrow".to_string(),
                            String::new(),
                            Applicability::MachineApplicable,
                            true,
                            true
                        ));
                    }
                    return None;
                }
                if sp.contains(expr.span)
                    && sm.is_span_accessible(expr.span)
                {
                    return Some((
                        sp.with_hi(expr.span.lo()),
                        "consider removing the borrow".to_string(),
                        String::new(),
                        Applicability::MachineApplicable,
                        true,
                        true,
                    ));
                }
            }
            (
                _,
                &ty::RawPtr(TypeAndMut { ty: ty_b, mutbl: mutbl_b }),
                &ty::Ref(_, ty_a, mutbl_a),
            ) => {
                if let Some(steps) = self.deref_steps(ty_a, ty_b)
                    // Only suggest valid if dereferencing needed.
                    && steps > 0
                    // The pointer type implements `Copy` trait so the suggestion is always valid.
                    && let Ok(src) = sm.span_to_snippet(sp)
                {
                    let derefs = "*".repeat(steps);
                    if let Some((span, src, applicability)) = match mutbl_b {
                        hir::Mutability::Mut => {
                            let new_prefix = "&mut ".to_owned() + &derefs;
                            match mutbl_a {
                                hir::Mutability::Mut => {
                                    replace_prefix(&src, "&mut ", &new_prefix).map(|_| {
                                        let pos = sp.lo() + BytePos(5);
                                        let sp = sp.with_lo(pos).with_hi(pos);
                                        (sp, derefs, Applicability::MachineApplicable)
                                    })
                                }
                                hir::Mutability::Not => {
                                    replace_prefix(&src, "&", &new_prefix).map(|_| {
                                        let pos = sp.lo() + BytePos(1);
                                        let sp = sp.with_lo(pos).with_hi(pos);
                                        (
                                            sp,
                                            format!("mut {derefs}"),
                                            Applicability::Unspecified,
                                        )
                                    })
                                }
                            }
                        }
                        hir::Mutability::Not => {
                            let new_prefix = "&".to_owned() + &derefs;
                            match mutbl_a {
                                hir::Mutability::Mut => {
                                    replace_prefix(&src, "&mut ", &new_prefix).map(|_| {
                                        let lo = sp.lo() + BytePos(1);
                                        let hi = sp.lo() + BytePos(5);
                                        let sp = sp.with_lo(lo).with_hi(hi);
                                        (sp, derefs, Applicability::MachineApplicable)
                                    })
                                }
                                hir::Mutability::Not => {
                                    replace_prefix(&src, "&", &new_prefix).map(|_| {
                                        let pos = sp.lo() + BytePos(1);
                                        let sp = sp.with_lo(pos).with_hi(pos);
                                        (sp, derefs, Applicability::MachineApplicable)
                                    })
                                }
                            }
                        }
                    } {
                        return Some((
                            span,
                            "consider dereferencing".to_string(),
                            src,
                            applicability,
                            true,
                            false,
                        ));
                    }
                }
            }
            _ if sp == expr.span => {
                if let Some(mut steps) = self.deref_steps(checked_ty, expected) {
                    let mut expr = expr.peel_blocks();
                    let mut prefix_span = expr.span.shrink_to_lo();
                    let mut remove = String::new();

                    // Try peeling off any existing `&` and `&mut` to reach our target type
                    while steps > 0 {
                        if let hir::ExprKind::AddrOf(_, mutbl, inner) = expr.kind {
                            // If the expression has `&`, removing it would fix the error
                            prefix_span = prefix_span.with_hi(inner.span.lo());
                            expr = inner;
                            remove += match mutbl {
                                hir::Mutability::Not => "&",
                                hir::Mutability::Mut => "&mut ",
                            };
                            steps -= 1;
                        } else {
                            break;
                        }
                    }
                    // If we've reached our target type with just removing `&`, then just print now.
                    if steps == 0 {
                        return Some((
                            prefix_span,
                            format!("consider removing the `{}`", remove.trim()),
                            String::new(),
                            // Do not remove `&&` to get to bool, because it might be something like
                            // { a } && b, which we have a separate fixup suggestion that is more
                            // likely correct...
                            if remove.trim() == "&&" && expected == self.tcx.types.bool {
                                Applicability::MaybeIncorrect
                            } else {
                                Applicability::MachineApplicable
                            },
                            true,
                            false,
                        ));
                    }

                    // For this suggestion to make sense, the type would need to be `Copy`,
                    // or we have to be moving out of a `Box<T>`
                    if self.type_is_copy_modulo_regions(self.param_env, expected, sp)
                        // FIXME(compiler-errors): We can actually do this if the checked_ty is
                        // `steps` layers of boxes, not just one, but this is easier and most likely.
                        || (checked_ty.is_box() && steps == 1)
                    {
                        let deref_kind = if checked_ty.is_box() {
                            "unboxing the value"
                        } else if checked_ty.is_region_ptr() {
                            "dereferencing the borrow"
                        } else {
                            "dereferencing the type"
                        };

                        // Suggest removing `&` if we have removed any, otherwise suggest just
                        // dereferencing the remaining number of steps.
                        let message = if remove.is_empty() {
                            format!("consider {deref_kind}")
                        } else {
                            format!(
                                "consider removing the `{}` and {} instead",
                                remove.trim(),
                                deref_kind
                            )
                        };

                        let prefix = match self.maybe_get_struct_pattern_shorthand_field(expr) {
                            Some(ident) => format!("{ident}: "),
                            None => String::new(),
                        };

                        let (span, suggestion) = if self.is_else_if_block(expr) {
                            // Don't suggest nonsense like `else *if`
                            return None;
                        } else if let Some(expr) = self.maybe_get_block_expr(expr) {
                            // prefix should be empty here..
                            (expr.span.shrink_to_lo(), "*".to_string())
                        } else {
                            (prefix_span, format!("{}{}", prefix, "*".repeat(steps)))
                        };

                        return Some((
                            span,
                            message,
                            suggestion,
                            Applicability::MachineApplicable,
                            true,
                            false,
                        ));
                    }
                }
            }
            _ => {}
        }
        None
    }

    pub fn check_for_cast(
        &self,
        err: &mut Diagnostic,
        expr: &hir::Expr<'_>,
        checked_ty: Ty<'tcx>,
        expected_ty: Ty<'tcx>,
        expected_ty_expr: Option<&'tcx hir::Expr<'tcx>>,
    ) -> bool {
        if self.tcx.sess.source_map().is_imported(expr.span) {
            // Ignore if span is from within a macro.
            return false;
        }

        let Ok(src) = self.tcx.sess.source_map().span_to_snippet(expr.span) else {
            return false;
        };

        // If casting this expression to a given numeric type would be appropriate in case of a type
        // mismatch.
        //
        // We want to minimize the amount of casting operations that are suggested, as it can be a
        // lossy operation with potentially bad side effects, so we only suggest when encountering
        // an expression that indicates that the original type couldn't be directly changed.
        //
        // For now, don't suggest casting with `as`.
        let can_cast = false;

        let mut sugg = vec![];

        if let Some(hir::Node::ExprField(field)) =
            self.tcx.hir().find(self.tcx.hir().get_parent_node(expr.hir_id))
        {
            // `expr` is a literal field for a struct, only suggest if appropriate
            if field.is_shorthand {
                // This is a field literal
                sugg.push((field.ident.span.shrink_to_lo(), format!("{}: ", field.ident)));
            } else {
                // Likely a field was meant, but this field wasn't found. Do not suggest anything.
                return false;
            }
        };

        if let hir::ExprKind::Call(path, args) = &expr.kind
            && let (hir::ExprKind::Path(hir::QPath::TypeRelative(base_ty, path_segment)), 1) =
                (&path.kind, args.len())
            // `expr` is a conversion like `u32::from(val)`, do not suggest anything (#63697).
            && let (hir::TyKind::Path(hir::QPath::Resolved(None, base_ty_path)), sym::from) =
                (&base_ty.kind, path_segment.ident.name)
        {
            if let Some(ident) = &base_ty_path.segments.iter().map(|s| s.ident).next() {
                match ident.name {
                    sym::i128
                    | sym::i64
                    | sym::i32
                    | sym::i16
                    | sym::i8
                    | sym::u128
                    | sym::u64
                    | sym::u32
                    | sym::u16
                    | sym::u8
                    | sym::isize
                    | sym::usize
                        if base_ty_path.segments.len() == 1 =>
                    {
                        return false;
                    }
                    _ => {}
                }
            }
        }

        let msg = format!(
            "you can convert {} `{}` to {} `{}`",
            checked_ty.kind().article(),
            checked_ty,
            expected_ty.kind().article(),
            expected_ty,
        );
        let cast_msg = format!(
            "you can cast {} `{}` to {} `{}`",
            checked_ty.kind().article(),
            checked_ty,
            expected_ty.kind().article(),
            expected_ty,
        );
        let lit_msg = format!(
            "change the type of the numeric literal from `{checked_ty}` to `{expected_ty}`",
        );

        let close_paren = if expr.precedence().order() < PREC_POSTFIX {
            sugg.push((expr.span.shrink_to_lo(), "(".to_string()));
            ")"
        } else {
            ""
        };

        let mut cast_suggestion = sugg.clone();
        cast_suggestion.push((expr.span.shrink_to_hi(), format!("{close_paren} as {expected_ty}")));
        let mut into_suggestion = sugg.clone();
        into_suggestion.push((expr.span.shrink_to_hi(), format!("{close_paren}.into()")));
        let mut suffix_suggestion = sugg.clone();
        suffix_suggestion.push((
            if matches!(
                (&expected_ty.kind(), &checked_ty.kind()),
                (ty::Int(_) | ty::Uint(_), ty::Float(_))
            ) {
                // Remove fractional part from literal, for example `42.0f32` into `42`
                let src = src.trim_end_matches(&checked_ty.to_string());
                let len = src.split('.').next().unwrap().len();
                expr.span.with_lo(expr.span.lo() + BytePos(len as u32))
            } else {
                let len = src.trim_end_matches(&checked_ty.to_string()).len();
                expr.span.with_lo(expr.span.lo() + BytePos(len as u32))
            },
            if expr.precedence().order() < PREC_POSTFIX {
                // Readd `)`
                format!("{expected_ty})")
            } else {
                expected_ty.to_string()
            },
        ));
        let literal_is_ty_suffixed = |expr: &hir::Expr<'_>| {
            if let hir::ExprKind::Lit(lit) = &expr.kind { lit.node.is_suffixed() } else { false }
        };
        let is_negative_int =
            |expr: &hir::Expr<'_>| matches!(expr.kind, hir::ExprKind::Unary(hir::UnOp::Neg, ..));
        let is_uint = |ty: Ty<'_>| matches!(ty.kind(), ty::Uint(..));

        let in_const_context = self.tcx.hir().is_inside_const_context(expr.hir_id);

        let suggest_fallible_into_or_lhs_from =
            |err: &mut Diagnostic, exp_to_found_is_fallible: bool| {
                // If we know the expression the expected type is derived from, we might be able
                // to suggest a widening conversion rather than a narrowing one (which may
                // panic). For example, given x: u8 and y: u32, if we know the span of "x",
                //   x > y
                // can be given the suggestion "u32::from(x) > y" rather than
                // "x > y.try_into().unwrap()".
                let lhs_expr_and_src = expected_ty_expr.and_then(|expr| {
                    self.tcx
                        .sess
                        .source_map()
                        .span_to_snippet(expr.span)
                        .ok()
                        .map(|src| (expr, src))
                });
                let (msg, suggestion) = if let (Some((lhs_expr, lhs_src)), false) =
                    (lhs_expr_and_src, exp_to_found_is_fallible)
                {
                    let msg = format!(
                        "you can convert `{lhs_src}` from `{expected_ty}` to `{checked_ty}`, matching the type of `{src}`",
                    );
                    let suggestion = vec![
                        (lhs_expr.span.shrink_to_lo(), format!("{checked_ty}::from(")),
                        (lhs_expr.span.shrink_to_hi(), ")".to_string()),
                    ];
                    (msg, suggestion)
                } else {
                    let msg = format!("{msg} and panic if the converted value doesn't fit");
                    let mut suggestion = sugg.clone();
                    suggestion.push((
                        expr.span.shrink_to_hi(),
                        format!("{close_paren}.try_into().unwrap()"),
                    ));
                    (msg, suggestion)
                };
                err.multipart_suggestion_verbose(
                    &msg,
                    suggestion,
                    Applicability::MachineApplicable,
                );
            };

        let suggest_to_change_suffix_or_into =
            |err: &mut Diagnostic,
             found_to_exp_is_fallible: bool,
             exp_to_found_is_fallible: bool| {
                let exp_is_lhs =
                    expected_ty_expr.map(|e| self.tcx.hir().is_lhs(e.hir_id)).unwrap_or(false);

                if exp_is_lhs {
                    return;
                }

                let always_fallible = found_to_exp_is_fallible
                    && (exp_to_found_is_fallible || expected_ty_expr.is_none());
                let msg = if literal_is_ty_suffixed(expr) {
                    &lit_msg
                } else if always_fallible && (is_negative_int(expr) && is_uint(expected_ty)) {
                    // We now know that converting either the lhs or rhs is fallible. Before we
                    // suggest a fallible conversion, check if the value can never fit in the
                    // expected type.
                    let msg = format!("`{src}` cannot fit into type `{expected_ty}`");
                    err.note(&msg);
                    return;
                } else if in_const_context {
                    // Do not recommend `into` or `try_into` in const contexts.
                    return;
                } else if found_to_exp_is_fallible {
                    return suggest_fallible_into_or_lhs_from(err, exp_to_found_is_fallible);
                } else {
                    &msg
                };
                let suggestion = if literal_is_ty_suffixed(expr) {
                    suffix_suggestion.clone()
                } else {
                    into_suggestion.clone()
                };
                err.multipart_suggestion_verbose(msg, suggestion, Applicability::MachineApplicable);
            };

        match (&expected_ty.kind(), &checked_ty.kind()) {
            (&ty::Int(ref exp), &ty::Int(ref found)) => {
                let (f2e_is_fallible, e2f_is_fallible) = match (exp.bit_width(), found.bit_width())
                {
                    (Some(exp), Some(found)) if exp < found => (true, false),
                    (Some(exp), Some(found)) if exp > found => (false, true),
                    (None, Some(8 | 16)) => (false, true),
                    (Some(8 | 16), None) => (true, false),
                    (None, _) | (_, None) => (true, true),
                    _ => (false, false),
                };
                suggest_to_change_suffix_or_into(err, f2e_is_fallible, e2f_is_fallible);
                true
            }
            (&ty::Uint(ref exp), &ty::Uint(ref found)) => {
                let (f2e_is_fallible, e2f_is_fallible) = match (exp.bit_width(), found.bit_width())
                {
                    (Some(exp), Some(found)) if exp < found => (true, false),
                    (Some(exp), Some(found)) if exp > found => (false, true),
                    (None, Some(8 | 16)) => (false, true),
                    (Some(8 | 16), None) => (true, false),
                    (None, _) | (_, None) => (true, true),
                    _ => (false, false),
                };
                suggest_to_change_suffix_or_into(err, f2e_is_fallible, e2f_is_fallible);
                true
            }
            (&ty::Int(exp), &ty::Uint(found)) => {
                let (f2e_is_fallible, e2f_is_fallible) = match (exp.bit_width(), found.bit_width())
                {
                    (Some(exp), Some(found)) if found < exp => (false, true),
                    (None, Some(8)) => (false, true),
                    _ => (true, true),
                };
                suggest_to_change_suffix_or_into(err, f2e_is_fallible, e2f_is_fallible);
                true
            }
            (&ty::Uint(exp), &ty::Int(found)) => {
                let (f2e_is_fallible, e2f_is_fallible) = match (exp.bit_width(), found.bit_width())
                {
                    (Some(exp), Some(found)) if found > exp => (true, false),
                    (Some(8), None) => (true, false),
                    _ => (true, true),
                };
                suggest_to_change_suffix_or_into(err, f2e_is_fallible, e2f_is_fallible);
                true
            }
            (&ty::Float(ref exp), &ty::Float(ref found)) => {
                if found.bit_width() < exp.bit_width() {
                    suggest_to_change_suffix_or_into(err, false, true);
                } else if literal_is_ty_suffixed(expr) {
                    err.multipart_suggestion_verbose(
                        &lit_msg,
                        suffix_suggestion,
                        Applicability::MachineApplicable,
                    );
                } else if can_cast {
                    // Missing try_into implementation for `f64` to `f32`
                    err.multipart_suggestion_verbose(
                        &format!("{cast_msg}, producing the closest possible value"),
                        cast_suggestion,
                        Applicability::MaybeIncorrect, // lossy conversion
                    );
                }
                true
            }
            (&ty::Uint(_) | &ty::Int(_), &ty::Float(_)) => {
                if literal_is_ty_suffixed(expr) {
                    err.multipart_suggestion_verbose(
                        &lit_msg,
                        suffix_suggestion,
                        Applicability::MachineApplicable,
                    );
                } else if can_cast {
                    // Missing try_into implementation for `{float}` to `{integer}`
                    err.multipart_suggestion_verbose(
                        &format!("{msg}, rounding the float towards zero"),
                        cast_suggestion,
                        Applicability::MaybeIncorrect, // lossy conversion
                    );
                }
                true
            }
            (&ty::Float(ref exp), &ty::Uint(ref found)) => {
                // if `found` is `None` (meaning found is `usize`), don't suggest `.into()`
                if exp.bit_width() > found.bit_width().unwrap_or(256) {
                    err.multipart_suggestion_verbose(
                        &format!(
                            "{msg}, producing the floating point representation of the integer",
                        ),
                        into_suggestion,
                        Applicability::MachineApplicable,
                    );
                } else if literal_is_ty_suffixed(expr) {
                    err.multipart_suggestion_verbose(
                        &lit_msg,
                        suffix_suggestion,
                        Applicability::MachineApplicable,
                    );
                } else {
                    // Missing try_into implementation for `{integer}` to `{float}`
                    err.multipart_suggestion_verbose(
                        &format!(
                            "{cast_msg}, producing the floating point representation of the integer, \
                                 rounded if necessary",
                        ),
                        cast_suggestion,
                        Applicability::MaybeIncorrect, // lossy conversion
                    );
                }
                true
            }
            (&ty::Float(ref exp), &ty::Int(ref found)) => {
                // if `found` is `None` (meaning found is `isize`), don't suggest `.into()`
                if exp.bit_width() > found.bit_width().unwrap_or(256) {
                    err.multipart_suggestion_verbose(
                        &format!(
                            "{}, producing the floating point representation of the integer",
                            &msg,
                        ),
                        into_suggestion,
                        Applicability::MachineApplicable,
                    );
                } else if literal_is_ty_suffixed(expr) {
                    err.multipart_suggestion_verbose(
                        &lit_msg,
                        suffix_suggestion,
                        Applicability::MachineApplicable,
                    );
                } else {
                    // Missing try_into implementation for `{integer}` to `{float}`
                    err.multipart_suggestion_verbose(
                        &format!(
                            "{}, producing the floating point representation of the integer, \
                                rounded if necessary",
                            &msg,
                        ),
                        cast_suggestion,
                        Applicability::MaybeIncorrect, // lossy conversion
                    );
                }
                true
            }
            (
                &ty::Uint(ty::UintTy::U32 | ty::UintTy::U64 | ty::UintTy::U128)
                | &ty::Int(ty::IntTy::I32 | ty::IntTy::I64 | ty::IntTy::I128),
                &ty::Char,
            ) => {
                err.multipart_suggestion_verbose(
                    &format!("{cast_msg}, since a `char` always occupies 4 bytes"),
                    cast_suggestion,
                    Applicability::MachineApplicable,
                );
                true
            }
            _ => false,
        }
    }
}
