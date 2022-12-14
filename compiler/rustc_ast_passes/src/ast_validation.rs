// Validate AST before lowering it to HIR.
//
// This pass is supposed to catch things that fit into AST data structures,
// but not permitted by the language. It runs after expansion when AST is frozen,
// so it can check for erroneous constructions produced by syntax extensions.
// This pass is supposed to perform only simple checks not requiring name resolution
// or type checking or some other kind of complex analysis.

use itertools::{Either, Itertools};
use rustc_ast::ptr::P;
use rustc_ast::visit::{self, AssocCtxt, BoundKind, FnCtxt, FnKind, Visitor};
use rustc_ast::walk_list;
use rustc_ast::*;
use rustc_ast_pretty::pprust::{self, State};
use rustc_data_structures::fx::FxHashMap;
use rustc_errors::{error_code, fluent, pluralize, struct_span_err, Applicability};
use rustc_macros::Subdiagnostic;
use rustc_parse::validate_attr;
use rustc_session::lint::builtin::{
    DEPRECATED_WHERE_CLAUSE_LOCATION, MISSING_ABI, PATTERNS_IN_FNS_WITHOUT_BODY,
};
use rustc_session::lint::{BuiltinLintDiagnostics, LintBuffer};
use rustc_session::Session;
use rustc_span::source_map::Spanned;
use rustc_span::symbol::{kw, sym, Ident};
use rustc_span::Span;
use rustc_target::spec::abi;
use std::mem;
use std::ops::{Deref, DerefMut};

use crate::errors::*;

const MORE_EXTERN: &str =
    "for more information, visit https://doc.rust-lang.org/std/keyword.extern.html";

/// Is `self` allowed semantically as the first parameter in an `FnDecl`?
enum SelfSemantic {
    Yes,
    No,
}

/// What is the context that prevents using `~const`?
enum DisallowTildeConstContext<'a> {
    TraitObject,
    ImplTrait,
    Fn(FnKind<'a>),
}

struct AstValidator<'a> {
    session: &'a Session,

    /// The span of the `extern` in an `extern { ... }` block, if any.
    extern_mod: Option<&'a Item>,

    /// Are we inside a trait impl?
    in_trait_impl: bool,

    in_const_trait_impl: bool,

    has_proc_macro_decls: bool,

    /// Used to ban nested `impl Trait`, e.g., `impl Into<impl Debug>`.
    /// Nested `impl Trait` _is_ allowed in associated type position,
    /// e.g., `impl Iterator<Item = impl Debug>`.
    outer_impl_trait: Option<Span>,

    disallow_tilde_const: Option<DisallowTildeConstContext<'a>>,

    /// Used to ban `impl Trait` in path projections like `<impl Iterator>::Item`
    /// or `Foo::Bar<impl Trait>`
    is_impl_trait_banned: bool,

    /// Used to ban associated type bounds (i.e., `Type<AssocType: Bounds>`) in
    /// certain positions.
    is_assoc_ty_bound_banned: bool,

    /// See [ForbiddenLetReason]
    forbidden_let_reason: Option<ForbiddenLetReason>,

    lint_buffer: &'a mut LintBuffer,
}

impl<'a> AstValidator<'a> {
    fn with_in_trait_impl(
        &mut self,
        is_in: bool,
        constness: Option<Const>,
        f: impl FnOnce(&mut Self),
    ) {
        let old = mem::replace(&mut self.in_trait_impl, is_in);
        let old_const =
            mem::replace(&mut self.in_const_trait_impl, matches!(constness, Some(Const::Yes(_))));
        f(self);
        self.in_trait_impl = old;
        self.in_const_trait_impl = old_const;
    }

    fn with_banned_impl_trait(&mut self, f: impl FnOnce(&mut Self)) {
        let old = mem::replace(&mut self.is_impl_trait_banned, true);
        f(self);
        self.is_impl_trait_banned = old;
    }

    fn with_tilde_const(
        &mut self,
        disallowed: Option<DisallowTildeConstContext<'a>>,
        f: impl FnOnce(&mut Self),
    ) {
        let old = mem::replace(&mut self.disallow_tilde_const, disallowed);
        f(self);
        self.disallow_tilde_const = old;
    }

    fn with_tilde_const_allowed(&mut self, f: impl FnOnce(&mut Self)) {
        self.with_tilde_const(None, f)
    }

    fn with_banned_tilde_const(
        &mut self,
        ctx: DisallowTildeConstContext<'a>,
        f: impl FnOnce(&mut Self),
    ) {
        self.with_tilde_const(Some(ctx), f)
    }

    fn with_let_management(
        &mut self,
        forbidden_let_reason: Option<ForbiddenLetReason>,
        f: impl FnOnce(&mut Self, Option<ForbiddenLetReason>),
    ) {
        let old = mem::replace(&mut self.forbidden_let_reason, forbidden_let_reason);
        f(self, old);
        self.forbidden_let_reason = old;
    }

    /// Emits an error banning the `let` expression provided in the given location.
    fn ban_let_expr(&self, expr: &'a Expr, forbidden_let_reason: ForbiddenLetReason) {
        let sess = &self.session;
        if sess.opts.unstable_features.is_nightly_build() {
            sess.emit_err(ForbiddenLet { span: expr.span, reason: forbidden_let_reason });
        } else {
            sess.emit_err(ForbiddenLetStable { span: expr.span });
        }
    }

    fn check_gat_where(
        &mut self,
        id: NodeId,
        before_predicates: &[WherePredicate],
        where_clauses: (ast::TyAliasWhereClause, ast::TyAliasWhereClause),
    ) {
        if !before_predicates.is_empty() {
            let mut state = State::new();
            if !where_clauses.1.0 {
                state.space();
                state.word_space("where");
            } else {
                state.word_space(",");
            }
            let mut first = true;
            for p in before_predicates.iter() {
                if !first {
                    state.word_space(",");
                }
                first = false;
                state.print_where_predicate(p);
            }
            let suggestion = state.s.eof();
            self.lint_buffer.buffer_lint_with_diagnostic(
                DEPRECATED_WHERE_CLAUSE_LOCATION,
                id,
                where_clauses.0.1,
                fluent::ast_passes_deprecated_where_clause_location,
                BuiltinLintDiagnostics::DeprecatedWhereclauseLocation(
                    where_clauses.1.1.shrink_to_hi(),
                    suggestion,
                ),
            );
        }
    }

    fn with_banned_assoc_ty_bound(&mut self, f: impl FnOnce(&mut Self)) {
        let old = mem::replace(&mut self.is_assoc_ty_bound_banned, true);
        f(self);
        self.is_assoc_ty_bound_banned = old;
    }

    fn with_impl_trait(&mut self, outer: Option<Span>, f: impl FnOnce(&mut Self)) {
        let old = mem::replace(&mut self.outer_impl_trait, outer);
        if outer.is_some() {
            self.with_banned_tilde_const(DisallowTildeConstContext::ImplTrait, f);
        } else {
            f(self);
        }
        self.outer_impl_trait = old;
    }

    fn visit_assoc_constraint_from_generic_args(&mut self, constraint: &'a AssocConstraint) {
        match constraint.kind {
            AssocConstraintKind::Equality { .. } => {}
            AssocConstraintKind::Bound { .. } => {
                if self.is_assoc_ty_bound_banned {
                    self.session.emit_err(ForbiddenAssocConstraint { span: constraint.span });
                }
            }
        }
        self.visit_assoc_constraint(constraint);
    }

    // Mirrors `visit::walk_ty`, but tracks relevant state.
    fn walk_ty(&mut self, t: &'a Ty) {
        match t.kind {
            TyKind::ImplTrait(..) => {
                self.with_impl_trait(Some(t.span), |this| visit::walk_ty(this, t))
            }
            TyKind::TraitObject(..) => self
                .with_banned_tilde_const(DisallowTildeConstContext::TraitObject, |this| {
                    visit::walk_ty(this, t)
                }),
            TyKind::Path(ref qself, ref path) => {
                // We allow these:
                //  - `Option<impl Trait>`
                //  - `option::Option<impl Trait>`
                //  - `option::Option<T>::Foo<impl Trait>
                //
                // But not these:
                //  - `<impl Trait>::Foo`
                //  - `option::Option<impl Trait>::Foo`.
                //
                // To implement this, we disallow `impl Trait` from `qself`
                // (for cases like `<impl Trait>::Foo>`)
                // but we allow `impl Trait` in `GenericArgs`
                // iff there are no more PathSegments.
                if let Some(ref qself) = *qself {
                    // `impl Trait` in `qself` is always illegal
                    self.with_banned_impl_trait(|this| this.visit_ty(&qself.ty));
                }

                // Note that there should be a call to visit_path here,
                // so if any logic is added to process `Path`s a call to it should be
                // added both in visit_path and here. This code mirrors visit::walk_path.
                for (i, segment) in path.segments.iter().enumerate() {
                    // Allow `impl Trait` iff we're on the final path segment
                    if i == path.segments.len() - 1 {
                        self.visit_path_segment(segment);
                    } else {
                        self.with_banned_impl_trait(|this| this.visit_path_segment(segment));
                    }
                }
            }
            _ => visit::walk_ty(self, t),
        }
    }

    fn err_handler(&self) -> &rustc_errors::Handler {
        &self.session.diagnostic()
    }

    fn check_lifetime(&self, ident: Ident) {
        let valid_names = [kw::UnderscoreLifetime, kw::StaticLifetime, kw::Empty];
        if !valid_names.contains(&ident.name) && ident.without_first_quote().is_reserved() {
            self.session.emit_err(KeywordLifetime { span: ident.span });
        }
    }

    fn check_label(&self, ident: Ident) {
        if ident.without_first_quote().is_reserved() {
            self.session.emit_err(InvalidLabel { span: ident.span, name: ident.name });
        }
    }

    fn invalid_visibility(&self, vis: &Visibility, note: Option<InvalidVisibilityNote>) {
        if let VisibilityKind::Inherited = vis.kind {
            return;
        }

        self.session.emit_err(InvalidVisibility {
            span: vis.span,
            implied: if vis.kind.is_pub() { Some(vis.span) } else { None },
            note,
        });
    }

    fn check_decl_no_pat(decl: &FnDecl, mut report_err: impl FnMut(Span, Option<Ident>, bool)) {
        for Param { pat, .. } in &decl.inputs {
            match pat.kind {
                PatKind::Ident(BindingAnnotation::NONE, _, None) | PatKind::Wild => {}
                PatKind::Ident(BindingAnnotation::MUT, ident, None) => {
                    report_err(pat.span, Some(ident), true)
                }
                _ => report_err(pat.span, None, false),
            }
        }
    }

    fn check_trait_fn_not_const(&self, constness: Const) {
        if let Const::Yes(span) = constness {
            self.session.emit_err(TraitFnConst { span });
        }
    }

    fn check_late_bound_lifetime_defs(&self, params: &[GenericParam]) {
        // Check only lifetime parameters are present and that the lifetime
        // parameters that are present have no bounds.
        let non_lt_param_spans: Vec<_> = params
            .iter()
            .filter_map(|param| match param.kind {
                GenericParamKind::Lifetime { .. } => {
                    if !param.bounds.is_empty() {
                        let spans: Vec<_> = param.bounds.iter().map(|b| b.span()).collect();
                        self.session.emit_err(ForbiddenLifetimeBound { spans });
                    }
                    None
                }
                _ => Some(param.ident.span),
            })
            .collect();
        if !non_lt_param_spans.is_empty() {
            self.session.emit_err(ForbiddenNonLifetimeParam { spans: non_lt_param_spans });
        }
    }

    fn check_fn_decl(&self, fn_decl: &FnDecl, self_semantic: SelfSemantic) {
        self.check_decl_num_args(fn_decl);
        self.check_decl_cvaradic_pos(fn_decl);
        self.check_decl_attrs(fn_decl);
        self.check_decl_self_param(fn_decl, self_semantic);
    }

    /// Emits fatal error if function declaration has more than `u16::MAX` arguments
    /// Error is fatal to prevent errors during typechecking
    fn check_decl_num_args(&self, fn_decl: &FnDecl) {
        let max_num_args: usize = u16::MAX.into();
        if fn_decl.inputs.len() > max_num_args {
            let Param { span, .. } = fn_decl.inputs[0];
            self.session.emit_fatal(FnParamTooMany { span, max_num_args });
        }
    }

    fn check_decl_cvaradic_pos(&self, fn_decl: &FnDecl) {
        match &*fn_decl.inputs {
            [Param { ty, span, .. }] => {
                if let TyKind::CVarArgs = ty.kind {
                    self.session.emit_err(FnParamCVarArgsOnly { span: *span });
                }
            }
            [ps @ .., _] => {
                for Param { ty, span, .. } in ps {
                    if let TyKind::CVarArgs = ty.kind {
                        self.session.emit_err(FnParamCVarArgsNotLast { span: *span });
                    }
                }
            }
            _ => {}
        }
    }

    fn check_decl_attrs(&self, fn_decl: &FnDecl) {
        fn_decl
            .inputs
            .iter()
            .flat_map(|i| i.attrs.as_ref())
            .filter(|attr| {
                let arr = [
                    sym::allow,
                    sym::cfg,
                    sym::cfg_attr,
                    sym::deny,
                    sym::expect,
                    sym::forbid,
                    sym::warn,
                ];
                !arr.contains(&attr.name_or_empty()) && rustc_attr::is_builtin_attr(attr)
            })
            .for_each(|attr| {
                if attr.is_doc_comment() {
                    self.session.emit_err(FnParamDocComment { span: attr.span });
                } else {
                    self.session.emit_err(FnParamForbiddenAttr { span: attr.span });
                }
            });
    }

    fn check_decl_self_param(&self, fn_decl: &FnDecl, self_semantic: SelfSemantic) {
        if let (SelfSemantic::No, [param, ..]) = (self_semantic, &*fn_decl.inputs) {
            if param.is_self() {
                self.session.emit_err(FnParamForbiddenSelf { span: param.span });
            }
        }
    }

    fn check_defaultness(&self, span: Span, defaultness: Defaultness) {
        if let Defaultness::Default(def_span) = defaultness {
            let span = self.session.source_map().guess_head_span(span);
            self.session.emit_err(ForbiddenDefault { span, def_span });
        }
    }

    /// If `sp` ends with a semicolon, returns it as a `Span`
    /// Otherwise, returns `sp.shrink_to_hi()`
    fn ending_semi_or_hi(&self, sp: Span) -> Span {
        let source_map = self.session.source_map();
        let end = source_map.end_point(sp);

        if source_map.span_to_snippet(end).map(|s| s == ";").unwrap_or(false) {
            end
        } else {
            sp.shrink_to_hi()
        }
    }

    fn check_type_no_bounds(&self, bounds: &[GenericBound], ctx: &str) {
        let span = match bounds {
            [] => return,
            [b0] => b0.span(),
            [b0, .., bl] => b0.span().to(bl.span()),
        };
        self.err_handler()
            .struct_span_err(span, &format!("bounds on `type`s in {} have no effect", ctx))
            .emit();
    }

    fn check_foreign_ty_genericless(&self, generics: &Generics, where_span: Span) {
        let cannot_have = |span, descr, remove_descr| {
            self.err_handler()
                .struct_span_err(
                    span,
                    &format!("`type`s inside `extern` blocks cannot have {}", descr),
                )
                .span_suggestion(
                    span,
                    &format!("remove the {}", remove_descr),
                    "",
                    Applicability::MaybeIncorrect,
                )
                .span_label(self.current_extern_span(), "`extern` block begins here")
                .note(MORE_EXTERN)
                .emit();
        };

        if !generics.params.is_empty() {
            cannot_have(generics.span, "generic parameters", "generic parameters");
        }

        if !generics.where_clause.predicates.is_empty() {
            cannot_have(where_span, "`where` clauses", "`where` clause");
        }
    }

    fn check_foreign_kind_bodyless(&self, ident: Ident, kind: &str, body: Option<Span>) {
        let Some(body) = body else {
            return;
        };
        self.err_handler()
            .struct_span_err(ident.span, &format!("incorrect `{}` inside `extern` block", kind))
            .span_label(ident.span, "cannot have a body")
            .span_label(body, "the invalid body")
            .span_label(
                self.current_extern_span(),
                format!(
                    "`extern` blocks define existing foreign {0}s and {0}s \
                    inside of them cannot have a body",
                    kind
                ),
            )
            .note(MORE_EXTERN)
            .emit();
    }

    /// An `fn` in `extern { ... }` cannot have a body `{ ... }`.
    fn check_foreign_fn_bodyless(&self, ident: Ident, body: Option<&Block>) {
        let Some(body) = body else {
            return;
        };
        self.err_handler()
            .struct_span_err(ident.span, "incorrect function inside `extern` block")
            .span_label(ident.span, "cannot have a body")
            .span_suggestion(
                body.span,
                "remove the invalid body",
                ";",
                Applicability::MaybeIncorrect,
            )
            .help(
                "you might have meant to write a function accessible through FFI, \
                which can be done by writing `extern fn` outside of the `extern` block",
            )
            .span_label(
                self.current_extern_span(),
                "`extern` blocks define existing foreign functions and functions \
                inside of them cannot have a body",
            )
            .note(MORE_EXTERN)
            .emit();
    }

    fn current_extern_span(&self) -> Span {
        self.session.source_map().guess_head_span(self.extern_mod.unwrap().span)
    }

    /// An `fn` in `extern { ... }` cannot have qualifiers, e.g. `async fn`.
    fn check_foreign_fn_headerless(&self, ident: Ident, span: Span, header: FnHeader) {
        if header.has_qualifiers() {
            self.err_handler()
                .struct_span_err(ident.span, "functions in `extern` blocks cannot have qualifiers")
                .span_label(self.current_extern_span(), "in this `extern` block")
                .span_suggestion_verbose(
                    span.until(ident.span.shrink_to_lo()),
                    "remove the qualifiers",
                    "fn ",
                    Applicability::MaybeIncorrect,
                )
                .emit();
        }
    }

    /// An item in `extern { ... }` cannot use non-ascii identifier.
    fn check_foreign_item_ascii_only(&self, ident: Ident) {
        if !ident.as_str().is_ascii() {
            let n = 83942;
            self.err_handler()
                .struct_span_err(
                    ident.span,
                    "items in `extern` blocks cannot use non-ascii identifiers",
                )
                .span_label(self.current_extern_span(), "in this `extern` block")
                .note(&format!(
                    "this limitation may be lifted in the future; see issue #{} <https://github.com/rust-lang/rust/issues/{}> for more information",
                    n, n,
                ))
                .emit();
        }
    }

    /// Reject C-variadic type unless the function is foreign,
    /// or free and `unsafe extern "C"` semantically.
    fn check_c_variadic_type(&self, fk: FnKind<'a>) {
        match (fk.ctxt(), fk.header()) {
            (Some(FnCtxt::Foreign), _) => return,
            (Some(FnCtxt::Free), Some(header)) => match header.ext {
                Extern::Explicit(StrLit { symbol_unescaped: sym::C, .. }, _)
                | Extern::Implicit(_)
                    if matches!(header.unsafety, Unsafe::Yes(_)) =>
                {
                    return;
                }
                _ => {}
            },
            _ => {}
        };

        for Param { ty, span, .. } in &fk.decl().inputs {
            if let TyKind::CVarArgs = ty.kind {
                self.err_handler()
                    .struct_span_err(
                        *span,
                        "only foreign or `unsafe extern \"C\"` functions may be C-variadic",
                    )
                    .emit();
            }
        }
    }

    fn check_item_named(&self, ident: Ident, kind: &str) {
        if ident.name != kw::Underscore {
            return;
        }
        self.err_handler()
            .struct_span_err(ident.span, &format!("`{}` items in this context need a name", kind))
            .span_label(ident.span, format!("`_` is not a valid name for this `{}` item", kind))
            .emit();
    }

    fn check_nomangle_item_asciionly(&self, ident: Ident, item_span: Span) {
        if ident.name.as_str().is_ascii() {
            return;
        }
        let head_span = self.session.source_map().guess_head_span(item_span);
        struct_span_err!(
            self.session,
            head_span,
            E0754,
            "`#[no_mangle]` requires ASCII identifier"
        )
        .emit();
    }

    fn check_mod_file_item_asciionly(&self, ident: Ident) {
        if ident.name.as_str().is_ascii() {
            return;
        }
        struct_span_err!(
            self.session,
            ident.span,
            E0754,
            "trying to load file for module `{}` with non-ascii identifier name",
            ident.name
        )
        .help("consider using `#[path]` attribute to specify filesystem path")
        .emit();
    }

    fn deny_generic_params(&self, generics: &Generics, ident_span: Span) {
        if !generics.params.is_empty() {
            struct_span_err!(
                self.session,
                generics.span,
                E0567,
                "auto traits cannot have generic parameters"
            )
            .span_label(ident_span, "auto trait cannot have generic parameters")
            .span_suggestion(
                generics.span,
                "remove the parameters",
                "",
                Applicability::MachineApplicable,
            )
            .emit();
        }
    }

    fn emit_e0568(&self, span: Span, ident_span: Span) {
        struct_span_err!(
            self.session,
            span,
            E0568,
            "auto traits cannot have super traits or lifetime bounds"
        )
        .span_label(ident_span, "auto trait cannot have super traits or lifetime bounds")
        .span_suggestion(
            span,
            "remove the super traits or lifetime bounds",
            "",
            Applicability::MachineApplicable,
        )
        .emit();
    }

    fn deny_super_traits(&self, bounds: &GenericBounds, ident_span: Span) {
        if let [.., last] = &bounds[..] {
            let span = ident_span.shrink_to_hi().to(last.span());
            self.emit_e0568(span, ident_span);
        }
    }

    fn deny_where_clause(&self, where_clause: &WhereClause, ident_span: Span) {
        if !where_clause.predicates.is_empty() {
            self.emit_e0568(where_clause.span, ident_span);
        }
    }

    fn deny_items(&self, trait_items: &[P<AssocItem>], ident_span: Span) {
        if !trait_items.is_empty() {
            let spans: Vec<_> = trait_items.iter().map(|i| i.ident.span).collect();
            let total_span = trait_items.first().unwrap().span.to(trait_items.last().unwrap().span);
            struct_span_err!(
                self.session,
                spans,
                E0380,
                "auto traits cannot have associated items"
            )
            .span_suggestion(
                total_span,
                "remove these associated items",
                "",
                Applicability::MachineApplicable,
            )
            .span_label(ident_span, "auto trait cannot have associated items")
            .emit();
        }
    }

    fn correct_generic_order_suggestion(&self, data: &AngleBracketedArgs) -> String {
        // Lifetimes always come first.
        let lt_sugg = data.args.iter().filter_map(|arg| match arg {
            AngleBracketedArg::Arg(lt @ GenericArg::Lifetime(_)) => {
                Some(pprust::to_string(|s| s.print_generic_arg(lt)))
            }
            _ => None,
        });
        let args_sugg = data.args.iter().filter_map(|a| match a {
            AngleBracketedArg::Arg(GenericArg::Lifetime(_)) | AngleBracketedArg::Constraint(_) => {
                None
            }
            AngleBracketedArg::Arg(arg) => Some(pprust::to_string(|s| s.print_generic_arg(arg))),
        });
        // Constraints always come last.
        let constraint_sugg = data.args.iter().filter_map(|a| match a {
            AngleBracketedArg::Arg(_) => None,
            AngleBracketedArg::Constraint(c) => {
                Some(pprust::to_string(|s| s.print_assoc_constraint(c)))
            }
        });
        format!(
            "<{}>",
            lt_sugg.chain(args_sugg).chain(constraint_sugg).collect::<Vec<String>>().join(", ")
        )
    }

    /// Enforce generic args coming before constraints in `<...>` of a path segment.
    fn check_generic_args_before_constraints(&self, data: &AngleBracketedArgs) {
        // Early exit in case it's partitioned as it should be.
        if data.args.iter().is_partitioned(|arg| matches!(arg, AngleBracketedArg::Arg(_))) {
            return;
        }
        // Find all generic argument coming after the first constraint...
        let (constraint_spans, arg_spans): (Vec<Span>, Vec<Span>) =
            data.args.iter().partition_map(|arg| match arg {
                AngleBracketedArg::Constraint(c) => Either::Left(c.span),
                AngleBracketedArg::Arg(a) => Either::Right(a.span()),
            });
        let args_len = arg_spans.len();
        let constraint_len = constraint_spans.len();
        // ...and then error:
        self.err_handler()
            .struct_span_err(
                arg_spans.clone(),
                "generic arguments must come before the first constraint",
            )
            .span_label(constraint_spans[0], &format!("constraint{}", pluralize!(constraint_len)))
            .span_label(
                *arg_spans.iter().last().unwrap(),
                &format!("generic argument{}", pluralize!(args_len)),
            )
            .span_labels(constraint_spans, "")
            .span_labels(arg_spans, "")
            .span_suggestion_verbose(
                data.span,
                &format!(
                    "move the constraint{} after the generic argument{}",
                    pluralize!(constraint_len),
                    pluralize!(args_len)
                ),
                self.correct_generic_order_suggestion(&data),
                Applicability::MachineApplicable,
            )
            .emit();
    }

    fn visit_ty_common(&mut self, ty: &'a Ty) {
        match ty.kind {
            TyKind::BareFn(ref bfty) => {
                self.check_fn_decl(&bfty.decl, SelfSemantic::No);
                Self::check_decl_no_pat(&bfty.decl, |span, _, _| {
                    struct_span_err!(
                        self.session,
                        span,
                        E0561,
                        "patterns aren't allowed in function pointer types"
                    )
                    .emit();
                });
                self.check_late_bound_lifetime_defs(&bfty.generic_params);
                if let Extern::Implicit(_) = bfty.ext {
                    let sig_span = self.session.source_map().next_point(ty.span.shrink_to_lo());
                    self.maybe_lint_missing_abi(sig_span, ty.id);
                }
            }
            TyKind::TraitObject(ref bounds, ..) => {
                let mut any_lifetime_bounds = false;
                for bound in bounds {
                    if let GenericBound::Outlives(ref lifetime) = *bound {
                        if any_lifetime_bounds {
                            struct_span_err!(
                                self.session,
                                lifetime.ident.span,
                                E0226,
                                "only a single explicit lifetime bound is permitted"
                            )
                            .emit();
                            break;
                        }
                        any_lifetime_bounds = true;
                    }
                }
            }
            TyKind::ImplTrait(_, ref bounds) => {
                if self.is_impl_trait_banned {
                    struct_span_err!(
                        self.session,
                        ty.span,
                        E0667,
                        "`impl Trait` is not allowed in path parameters"
                    )
                    .emit();
                }

                if let Some(outer_impl_trait_sp) = self.outer_impl_trait {
                    struct_span_err!(
                        self.session,
                        ty.span,
                        E0666,
                        "nested `impl Trait` is not allowed"
                    )
                    .span_label(outer_impl_trait_sp, "outer `impl Trait`")
                    .span_label(ty.span, "nested `impl Trait` here")
                    .emit();
                }

                if !bounds.iter().any(|b| matches!(b, GenericBound::Trait(..))) {
                    self.err_handler().span_err(ty.span, "at least one trait must be specified");
                }
            }
            _ => {}
        }
    }

    fn maybe_lint_missing_abi(&mut self, span: Span, id: NodeId) {
        // FIXME(davidtwco): This is a hack to detect macros which produce spans of the
        // call site which do not have a macro backtrace. See #61963.
        let is_macro_callsite = self
            .session
            .source_map()
            .span_to_snippet(span)
            .map(|snippet| snippet.starts_with("#["))
            .unwrap_or(true);
        if !is_macro_callsite {
            self.lint_buffer.buffer_lint_with_diagnostic(
                MISSING_ABI,
                id,
                span,
                "extern declarations without an explicit ABI are deprecated",
                BuiltinLintDiagnostics::MissingAbi(span, abi::Abi::FALLBACK),
            )
        }
    }
}

/// Checks that generic parameters are in the correct order,
/// which is lifetimes, then types and then consts. (`<'a, T, const N: usize>`)
fn validate_generic_param_order(
    handler: &rustc_errors::Handler,
    generics: &[GenericParam],
    span: Span,
) {
    let mut max_param: Option<ParamKindOrd> = None;
    let mut out_of_order = FxHashMap::default();
    let mut param_idents = Vec::with_capacity(generics.len());

    for (idx, param) in generics.iter().enumerate() {
        let ident = param.ident;
        let (kind, bounds, span) = (&param.kind, &param.bounds, ident.span);
        let (ord_kind, ident) = match &param.kind {
            GenericParamKind::Lifetime => (ParamKindOrd::Lifetime, ident.to_string()),
            GenericParamKind::Type { default: _ } => (ParamKindOrd::TypeOrConst, ident.to_string()),
            GenericParamKind::Const { ref ty, kw_span: _, default: _ } => {
                let ty = pprust::ty_to_string(ty);
                (ParamKindOrd::TypeOrConst, format!("const {}: {}", ident, ty))
            }
        };
        param_idents.push((kind, ord_kind, bounds, idx, ident));
        match max_param {
            Some(max_param) if max_param > ord_kind => {
                let entry = out_of_order.entry(ord_kind).or_insert((max_param, vec![]));
                entry.1.push(span);
            }
            Some(_) | None => max_param = Some(ord_kind),
        };
    }

    if !out_of_order.is_empty() {
        let mut ordered_params = "<".to_string();
        param_idents.sort_by_key(|&(_, po, _, i, _)| (po, i));
        let mut first = true;
        for (kind, _, bounds, _, ident) in param_idents {
            if !first {
                ordered_params += ", ";
            }
            ordered_params += &ident;

            if !bounds.is_empty() {
                ordered_params += ": ";
                ordered_params += &pprust::bounds_to_string(&bounds);
            }

            match kind {
                GenericParamKind::Type { default: Some(default) } => {
                    ordered_params += " = ";
                    ordered_params += &pprust::ty_to_string(default);
                }
                GenericParamKind::Type { default: None } => (),
                GenericParamKind::Lifetime => (),
                GenericParamKind::Const { ty: _, kw_span: _, default: Some(default) } => {
                    ordered_params += " = ";
                    ordered_params += &pprust::expr_to_string(&*default.value);
                }
                GenericParamKind::Const { ty: _, kw_span: _, default: None } => (),
            }
            first = false;
        }

        ordered_params += ">";

        for (param_ord, (max_param, spans)) in &out_of_order {
            let mut err = handler.struct_span_err(
                spans.clone(),
                &format!(
                    "{} parameters must be declared prior to {} parameters",
                    param_ord, max_param,
                ),
            );
            err.span_suggestion(
                span,
                "reorder the parameters: lifetimes, then consts and types",
                &ordered_params,
                Applicability::MachineApplicable,
            );
            err.emit();
        }
    }
}

impl<'a> Visitor<'a> for AstValidator<'a> {
    fn visit_attribute(&mut self, attr: &Attribute) {
        validate_attr::check_meta(&self.session.parse_sess, attr);
    }

    fn visit_expr(&mut self, expr: &'a Expr) {
        self.with_let_management(Some(ForbiddenLetReason::GenericForbidden), |this, forbidden_let_reason| {
            match &expr.kind {
                ExprKind::Binary(Spanned { node: BinOpKind::Or, span }, lhs, rhs) => {
                    let local_reason = Some(ForbiddenLetReason::NotSupportedOr(*span));
                    this.with_let_management(local_reason, |this, _| this.visit_expr(lhs));
                    this.with_let_management(local_reason, |this, _| this.visit_expr(rhs));
                }
                ExprKind::If(cond, then, opt_else) => {
                    this.visit_block(then);
                    walk_list!(this, visit_expr, opt_else);
                    this.with_let_management(None, |this, _| this.visit_expr(cond));
                    return;
                }
                ExprKind::Let(..) if let Some(elem) = forbidden_let_reason => {
                    this.ban_let_expr(expr, elem);
                },
                ExprKind::Match(scrutinee, arms) => {
                    this.visit_expr(scrutinee);
                    for arm in arms {
                        this.visit_expr(&arm.body);
                        this.visit_pat(&arm.pat);
                        walk_list!(this, visit_attribute, &arm.attrs);
                        if let Some(guard) = &arm.guard && let ExprKind::Let(_, guard_expr, _) = &guard.kind {
                            this.with_let_management(None, |this, _| {
                                this.visit_expr(guard_expr)
                            });
                            return;
                        }
                    }
                }
                ExprKind::Paren(local_expr) => {
                    fn has_let_expr(expr: &Expr) -> bool {
                        match expr.kind {
                            ExprKind::Binary(_, ref lhs, ref rhs) => has_let_expr(lhs) || has_let_expr(rhs),
                            ExprKind::Let(..) => true,
                            _ => false,
                        }
                    }
                    let local_reason = if has_let_expr(local_expr) {
                        Some(ForbiddenLetReason::NotSupportedParentheses(local_expr.span))
                    }
                    else {
                        forbidden_let_reason
                    };
                    this.with_let_management(local_reason, |this, _| this.visit_expr(local_expr));
                }
                ExprKind::Binary(Spanned { node: BinOpKind::And, .. }, ..) => {
                    this.with_let_management(forbidden_let_reason, |this, _| visit::walk_expr(this, expr));
                    return;
                }
                ExprKind::While(cond, then, opt_label) => {
                    walk_list!(this, visit_label, opt_label);
                    this.visit_block(then);
                    this.with_let_management(None, |this, _| this.visit_expr(cond));
                    return;
                }
                _ => visit::walk_expr(this, expr),
            }
        });
    }

    fn visit_ty(&mut self, ty: &'a Ty) {
        self.visit_ty_common(ty);
        self.walk_ty(ty)
    }

    fn visit_label(&mut self, label: &'a Label) {
        self.check_label(label.ident);
        visit::walk_label(self, label);
    }

    fn visit_lifetime(&mut self, lifetime: &'a Lifetime, _: visit::LifetimeCtxt) {
        self.check_lifetime(lifetime.ident);
        visit::walk_lifetime(self, lifetime);
    }

    fn visit_field_def(&mut self, field: &'a FieldDef) {
        visit::walk_field_def(self, field)
    }

    fn visit_item(&mut self, item: &'a Item) {
        if item.attrs.iter().any(|attr| self.session.is_proc_macro_attr(attr)) {
            self.has_proc_macro_decls = true;
        }

        if self.session.contains_name(&item.attrs, sym::no_mangle) {
            self.check_nomangle_item_asciionly(item.ident, item.span);
        }

        match item.kind {
            ItemKind::Impl(box Impl {
                unsafety,
                polarity,
                defaultness: _,
                constness,
                ref generics,
                of_trait: Some(ref t),
                ref self_ty,
                ref items,
            }) => {
                self.with_in_trait_impl(true, Some(constness), |this| {
                    this.invalid_visibility(&item.vis, None);
                    if let TyKind::Err = self_ty.kind {
                        this.err_handler()
                            .struct_span_err(
                                item.span,
                                "`impl Trait for .. {}` is an obsolete syntax",
                            )
                            .help("use `auto trait Trait {}` instead")
                            .emit();
                    }
                    if let (Unsafe::Yes(span), ImplPolarity::Negative(sp)) = (unsafety, polarity) {
                        struct_span_err!(
                            this.session,
                            sp.to(t.path.span),
                            E0198,
                            "negative impls cannot be unsafe"
                        )
                        .span_label(sp, "negative because of this")
                        .span_label(span, "unsafe because of this")
                        .emit();
                    }

                    this.visit_vis(&item.vis);
                    this.visit_ident(item.ident);
                    if let Const::Yes(_) = constness {
                        this.with_tilde_const_allowed(|this| this.visit_generics(generics));
                    } else {
                        this.visit_generics(generics);
                    }
                    this.visit_trait_ref(t);
                    this.visit_ty(self_ty);

                    walk_list!(this, visit_assoc_item, items, AssocCtxt::Impl);
                });
                return; // Avoid visiting again.
            }
            ItemKind::Impl(box Impl {
                unsafety,
                polarity,
                defaultness,
                constness,
                generics: _,
                of_trait: None,
                ref self_ty,
                items: _,
            }) => {
                let error = |annotation_span, annotation| {
                    let mut err = self.err_handler().struct_span_err(
                        self_ty.span,
                        &format!("inherent impls cannot be {}", annotation),
                    );
                    err.span_label(annotation_span, &format!("{} because of this", annotation));
                    err.span_label(self_ty.span, "inherent impl for this type");
                    err
                };

                self.invalid_visibility(
                    &item.vis,
                    Some(InvalidVisibilityNote::IndividualImplItems),
                );
                if let Unsafe::Yes(span) = unsafety {
                    error(span, "unsafe").code(error_code!(E0197)).emit();
                }
                if let ImplPolarity::Negative(span) = polarity {
                    error(span, "negative").emit();
                }
                if let Defaultness::Default(def_span) = defaultness {
                    error(def_span, "`default`")
                        .note("only trait implementations may be annotated with `default`")
                        .emit();
                }
                if let Const::Yes(span) = constness {
                    error(span, "`const`")
                        .note("only trait implementations may be annotated with `const`")
                        .emit();
                }
            }
            ItemKind::Fn(box Fn { defaultness, ref sig, ref generics, ref body }) => {
                self.check_defaultness(item.span, defaultness);

                if body.is_none() {
                    self.session.emit_err(FnWithoutBody {
                        span: item.span,
                        replace_span: self.ending_semi_or_hi(item.span),
                        extern_block_suggestion: match sig.header.ext {
                            Extern::None => None,
                            Extern::Implicit(start_span) => Some(ExternBlockSuggestion {
                                start_span,
                                end_span: item.span.shrink_to_hi(),
                                abi: None,
                            }),
                            Extern::Explicit(abi, start_span) => Some(ExternBlockSuggestion {
                                start_span,
                                end_span: item.span.shrink_to_hi(),
                                abi: Some(abi.symbol_unescaped),
                            }),
                        },
                    });
                }

                self.visit_vis(&item.vis);
                self.visit_ident(item.ident);
                let kind =
                    FnKind::Fn(FnCtxt::Free, item.ident, sig, &item.vis, generics, body.as_deref());
                self.visit_fn(kind, item.span, item.id);
                walk_list!(self, visit_attribute, &item.attrs);
                return; // Avoid visiting again.
            }
            ItemKind::ForeignMod(ForeignMod { abi, unsafety, .. }) => {
                let old_item = mem::replace(&mut self.extern_mod, Some(item));
                self.invalid_visibility(
                    &item.vis,
                    Some(InvalidVisibilityNote::IndividualForeignItems),
                );
                if let Unsafe::Yes(span) = unsafety {
                    self.err_handler().span_err(span, "extern block cannot be declared unsafe");
                }
                if abi.is_none() {
                    self.maybe_lint_missing_abi(item.span, item.id);
                }
                visit::walk_item(self, item);
                self.extern_mod = old_item;
                return; // Avoid visiting again.
            }
            ItemKind::Enum(ref def, _) => {
                for variant in &def.variants {
                    self.invalid_visibility(&variant.vis, None);
                    for field in variant.data.fields() {
                        self.invalid_visibility(&field.vis, None);
                    }
                }
            }
            ItemKind::Trait(box Trait { is_auto, ref generics, ref bounds, ref items, .. }) => {
                if is_auto == IsAuto::Yes {
                    // Auto traits cannot have generics, super traits nor contain items.
                    self.deny_generic_params(generics, item.ident.span);
                    self.deny_super_traits(bounds, item.ident.span);
                    self.deny_where_clause(&generics.where_clause, item.ident.span);
                    self.deny_items(items, item.ident.span);
                }

                // Equivalent of `visit::walk_item` for `ItemKind::Trait` that inserts a bound
                // context for the supertraits.
                self.visit_vis(&item.vis);
                self.visit_ident(item.ident);
                self.visit_generics(generics);
                self.with_tilde_const_allowed(|this| {
                    walk_list!(this, visit_param_bound, bounds, BoundKind::SuperTraits)
                });
                walk_list!(self, visit_assoc_item, items, AssocCtxt::Trait);
                walk_list!(self, visit_attribute, &item.attrs);
                return;
            }
            ItemKind::Mod(unsafety, ref mod_kind) => {
                if let Unsafe::Yes(span) = unsafety {
                    self.err_handler().span_err(span, "module cannot be declared unsafe");
                }
                // Ensure that `path` attributes on modules are recorded as used (cf. issue #35584).
                if !matches!(mod_kind, ModKind::Loaded(_, Inline::Yes, _))
                    && !self.session.contains_name(&item.attrs, sym::path)
                {
                    self.check_mod_file_item_asciionly(item.ident);
                }
            }
            ItemKind::Union(ref vdata, ..) => {
                if vdata.fields().is_empty() {
                    self.err_handler().span_err(item.span, "unions cannot have zero fields");
                }
            }
            ItemKind::Const(def, .., None) => {
                self.check_defaultness(item.span, def);
                self.session.emit_err(ConstWithoutBody {
                    span: item.span,
                    replace_span: self.ending_semi_or_hi(item.span),
                });
            }
            ItemKind::Static(.., None) => {
                self.session.emit_err(StaticWithoutBody {
                    span: item.span,
                    replace_span: self.ending_semi_or_hi(item.span),
                });
            }
            ItemKind::TyAlias(box TyAlias {
                defaultness,
                where_clauses,
                ref bounds,
                ref ty,
                ..
            }) => {
                self.check_defaultness(item.span, defaultness);
                if ty.is_none() {
                    self.session.emit_err(TyAliasWithoutBody {
                        span: item.span,
                        replace_span: self.ending_semi_or_hi(item.span),
                    });
                }
                self.check_type_no_bounds(bounds, "this context");
                if where_clauses.1.0 {
                    let mut err = self.err_handler().struct_span_err(
                        where_clauses.1.1,
                        "where clauses are not allowed after the type for type aliases",
                    );
                    err.note(
                        "see issue #89122 <https://github.com/rust-lang/rust/issues/89122> for more information",
                    );
                    err.emit();
                }
            }
            _ => {}
        }

        visit::walk_item(self, item);
    }

    fn visit_foreign_item(&mut self, fi: &'a ForeignItem) {
        match &fi.kind {
            ForeignItemKind::Fn(box Fn { defaultness, sig, body, .. }) => {
                self.check_defaultness(fi.span, *defaultness);
                self.check_foreign_fn_bodyless(fi.ident, body.as_deref());
                self.check_foreign_fn_headerless(fi.ident, fi.span, sig.header);
                self.check_foreign_item_ascii_only(fi.ident);
            }
            ForeignItemKind::TyAlias(box TyAlias {
                defaultness,
                generics,
                where_clauses,
                bounds,
                ty,
                ..
            }) => {
                self.check_defaultness(fi.span, *defaultness);
                self.check_foreign_kind_bodyless(fi.ident, "type", ty.as_ref().map(|b| b.span));
                self.check_type_no_bounds(bounds, "`extern` blocks");
                self.check_foreign_ty_genericless(generics, where_clauses.0.1);
                self.check_foreign_item_ascii_only(fi.ident);
            }
            ForeignItemKind::Static(_, _, body) => {
                self.check_foreign_kind_bodyless(fi.ident, "static", body.as_ref().map(|b| b.span));
                self.check_foreign_item_ascii_only(fi.ident);
            }
            ForeignItemKind::MacCall(..) => {}
        }

        visit::walk_foreign_item(self, fi)
    }

    // Mirrors `visit::walk_generic_args`, but tracks relevant state.
    fn visit_generic_args(&mut self, generic_args: &'a GenericArgs) {
        match *generic_args {
            GenericArgs::AngleBracketed(ref data) => {
                self.check_generic_args_before_constraints(data);

                for arg in &data.args {
                    match arg {
                        AngleBracketedArg::Arg(arg) => self.visit_generic_arg(arg),
                        // Type bindings such as `Item = impl Debug` in `Iterator<Item = Debug>`
                        // are allowed to contain nested `impl Trait`.
                        AngleBracketedArg::Constraint(constraint) => {
                            self.with_impl_trait(None, |this| {
                                this.visit_assoc_constraint_from_generic_args(constraint);
                            });
                        }
                    }
                }
            }
            GenericArgs::Parenthesized(ref data) => {
                walk_list!(self, visit_ty, &data.inputs);
                if let FnRetTy::Ty(ty) = &data.output {
                    // `-> Foo` syntax is essentially an associated type binding,
                    // so it is also allowed to contain nested `impl Trait`.
                    self.with_impl_trait(None, |this| this.visit_ty(ty));
                }
            }
        }
    }

    fn visit_generics(&mut self, generics: &'a Generics) {
        let mut prev_param_default = None;
        for param in &generics.params {
            match param.kind {
                GenericParamKind::Lifetime => (),
                GenericParamKind::Type { default: Some(_), .. }
                | GenericParamKind::Const { default: Some(_), .. } => {
                    prev_param_default = Some(param.ident.span);
                }
                GenericParamKind::Type { .. } | GenericParamKind::Const { .. } => {
                    if let Some(span) = prev_param_default {
                        let mut err = self.err_handler().struct_span_err(
                            span,
                            "generic parameters with a default must be trailing",
                        );
                        err.emit();
                        break;
                    }
                }
            }
        }

        validate_generic_param_order(self.err_handler(), &generics.params, generics.span);

        for predicate in &generics.where_clause.predicates {
            if let WherePredicate::EqPredicate(ref predicate) = *predicate {
                deny_equality_constraints(self, predicate, generics);
            }
        }
        walk_list!(self, visit_generic_param, &generics.params);
        for predicate in &generics.where_clause.predicates {
            match predicate {
                WherePredicate::BoundPredicate(bound_pred) => {
                    // A type binding, eg `for<'c> Foo: Send+Clone+'c`
                    self.check_late_bound_lifetime_defs(&bound_pred.bound_generic_params);

                    // This is slightly complicated. Our representation for poly-trait-refs contains a single
                    // binder and thus we only allow a single level of quantification. However,
                    // the syntax of Rust permits quantification in two places in where clauses,
                    // e.g., `T: for <'a> Foo<'a>` and `for <'a, 'b> &'b T: Foo<'a>`. If both are
                    // defined, then error.
                    if !bound_pred.bound_generic_params.is_empty() {
                        for bound in &bound_pred.bounds {
                            match bound {
                                GenericBound::Trait(t, _) => {
                                    if !t.bound_generic_params.is_empty() {
                                        struct_span_err!(
                                            self.err_handler(),
                                            t.span,
                                            E0316,
                                            "nested quantification of lifetimes"
                                        )
                                        .emit();
                                    }
                                }
                                GenericBound::Outlives(_) => {}
                            }
                        }
                    }
                }
                _ => {}
            }
            self.visit_where_predicate(predicate);
        }
    }

    fn visit_generic_param(&mut self, param: &'a GenericParam) {
        if let GenericParamKind::Lifetime { .. } = param.kind {
            self.check_lifetime(param.ident);
        }
        visit::walk_generic_param(self, param);
    }

    fn visit_param_bound(&mut self, bound: &'a GenericBound, ctxt: BoundKind) {
        if let GenericBound::Trait(ref poly, modify) = *bound {
            match (ctxt, modify) {
                (BoundKind::SuperTraits, TraitBoundModifier::Maybe) => {
                    let mut err = self
                        .err_handler()
                        .struct_span_err(poly.span, "`?Trait` is not permitted in supertraits");
                    let path_str = pprust::path_to_string(&poly.trait_ref.path);
                    err.note(&format!("traits are `?{}` by default", path_str));
                    err.emit();
                }
                (BoundKind::TraitObject, TraitBoundModifier::Maybe) => {
                    let mut err = self.err_handler().struct_span_err(
                        poly.span,
                        "`?Trait` is not permitted in trait object types",
                    );
                    err.emit();
                }
                (_, TraitBoundModifier::MaybeConst) if let Some(reason) = &self.disallow_tilde_const => {
                    let mut err = self.err_handler().struct_span_err(bound.span(), "`~const` is not allowed here");
                    match reason {
                        DisallowTildeConstContext::TraitObject => err.note("trait objects cannot have `~const` trait bounds"),
                        DisallowTildeConstContext::ImplTrait => err.note("`impl Trait`s cannot have `~const` trait bounds"),
                        DisallowTildeConstContext::Fn(FnKind::Closure(..)) => err.note("closures cannot have `~const` trait bounds"),
                        DisallowTildeConstContext::Fn(FnKind::Fn(_, ident, ..)) => err.span_note(ident.span, "this function is not `const`, so it cannot have `~const` trait bounds"),
                    };
                    err.emit();
                }
                (_, TraitBoundModifier::MaybeConstMaybe) => {
                    self.err_handler()
                        .span_err(bound.span(), "`~const` and `?` are mutually exclusive");
                }
                _ => {}
            }
        }

        visit::walk_param_bound(self, bound)
    }

    fn visit_poly_trait_ref(&mut self, t: &'a PolyTraitRef) {
        self.check_late_bound_lifetime_defs(&t.bound_generic_params);
        visit::walk_poly_trait_ref(self, t);
    }

    fn visit_variant_data(&mut self, s: &'a VariantData) {
        self.with_banned_assoc_ty_bound(|this| visit::walk_struct_def(this, s))
    }

    fn visit_enum_def(&mut self, enum_definition: &'a EnumDef) {
        self.with_banned_assoc_ty_bound(|this| visit::walk_enum_def(this, enum_definition))
    }

    fn visit_fn(&mut self, fk: FnKind<'a>, span: Span, id: NodeId) {
        // Only associated `fn`s can have `self` parameters.
        let self_semantic = match fk.ctxt() {
            Some(FnCtxt::Assoc(_)) => SelfSemantic::Yes,
            _ => SelfSemantic::No,
        };
        self.check_fn_decl(fk.decl(), self_semantic);

        self.check_c_variadic_type(fk);

        // Functions cannot both be `const async`
        if let Some(FnHeader {
            constness: Const::Yes(cspan),
            asyncness: Async::Yes { span: aspan, .. },
            ..
        }) = fk.header()
        {
            self.err_handler()
                .struct_span_err(
                    vec![*cspan, *aspan],
                    "functions cannot be both `const` and `async`",
                )
                .span_label(*cspan, "`const` because of this")
                .span_label(*aspan, "`async` because of this")
                .span_label(span, "") // Point at the fn header.
                .emit();
        }

        if let FnKind::Closure(ClosureBinder::For { generic_params, .. }, ..) = fk {
            self.check_late_bound_lifetime_defs(generic_params);
        }

        if let FnKind::Fn(
            _,
            _,
            FnSig { span: sig_span, header: FnHeader { ext: Extern::Implicit(_), .. }, .. },
            _,
            _,
            _,
        ) = fk
        {
            self.maybe_lint_missing_abi(*sig_span, id);
        }

        // Functions without bodies cannot have patterns.
        if let FnKind::Fn(ctxt, _, sig, _, _, None) = fk {
            Self::check_decl_no_pat(&sig.decl, |span, ident, mut_ident| {
                let (code, msg, label) = match ctxt {
                    FnCtxt::Foreign => (
                        error_code!(E0130),
                        "patterns aren't allowed in foreign function declarations",
                        "pattern not allowed in foreign function",
                    ),
                    _ => (
                        error_code!(E0642),
                        "patterns aren't allowed in functions without bodies",
                        "pattern not allowed in function without body",
                    ),
                };
                if mut_ident && matches!(ctxt, FnCtxt::Assoc(_)) {
                    if let Some(ident) = ident {
                        let diag = BuiltinLintDiagnostics::PatternsInFnsWithoutBody(span, ident);
                        self.lint_buffer.buffer_lint_with_diagnostic(
                            PATTERNS_IN_FNS_WITHOUT_BODY,
                            id,
                            span,
                            msg,
                            diag,
                        )
                    }
                } else {
                    self.err_handler()
                        .struct_span_err(span, msg)
                        .span_label(span, label)
                        .code(code)
                        .emit();
                }
            });
        }

        let tilde_const_allowed =
            matches!(fk.header(), Some(FnHeader { constness: ast::Const::Yes(_), .. }))
                || matches!(fk.ctxt(), Some(FnCtxt::Assoc(_)));

        let disallowed = (!tilde_const_allowed).then(|| DisallowTildeConstContext::Fn(fk));

        self.with_tilde_const(disallowed, |this| visit::walk_fn(this, fk));
    }

    fn visit_assoc_item(&mut self, item: &'a AssocItem, ctxt: AssocCtxt) {
        if self.session.contains_name(&item.attrs, sym::no_mangle) {
            self.check_nomangle_item_asciionly(item.ident, item.span);
        }

        if ctxt == AssocCtxt::Trait || !self.in_trait_impl {
            self.check_defaultness(item.span, item.kind.defaultness());
        }

        if ctxt == AssocCtxt::Impl {
            match &item.kind {
                AssocItemKind::Const(_, _, body) => {
                    if body.is_none() {
                        self.session.emit_err(AssocConstWithoutBody {
                            span: item.span,
                            replace_span: self.ending_semi_or_hi(item.span),
                        });
                    }
                }
                AssocItemKind::Fn(box Fn { body, .. }) => {
                    if body.is_none() {
                        self.session.emit_err(AssocFnWithoutBody {
                            span: item.span,
                            replace_span: self.ending_semi_or_hi(item.span),
                        });
                    }
                }
                AssocItemKind::Type(box TyAlias {
                    generics,
                    where_clauses,
                    where_predicates_split,
                    bounds,
                    ty,
                    ..
                }) => {
                    if ty.is_none() {
                        self.session.emit_err(AssocTypeWithoutBody {
                            span: item.span,
                            replace_span: self.ending_semi_or_hi(item.span),
                        });
                    }
                    self.check_type_no_bounds(bounds, "`impl`s");
                    if ty.is_some() {
                        self.check_gat_where(
                            item.id,
                            generics.where_clause.predicates.split_at(*where_predicates_split).0,
                            *where_clauses,
                        );
                    }
                }
                _ => {}
            }
        }

        if ctxt == AssocCtxt::Trait || self.in_trait_impl {
            self.invalid_visibility(&item.vis, None);
            if let AssocItemKind::Fn(box Fn { sig, .. }) = &item.kind {
                self.check_trait_fn_not_const(sig.header.constness);
            }
        }

        if let AssocItemKind::Const(..) = item.kind {
            self.check_item_named(item.ident, "const");
        }

        match item.kind {
            AssocItemKind::Type(box TyAlias { ref generics, ref bounds, ref ty, .. })
                if ctxt == AssocCtxt::Trait =>
            {
                self.visit_vis(&item.vis);
                self.visit_ident(item.ident);
                walk_list!(self, visit_attribute, &item.attrs);
                self.with_tilde_const_allowed(|this| {
                    this.visit_generics(generics);
                    walk_list!(this, visit_param_bound, bounds, BoundKind::Bound);
                });
                walk_list!(self, visit_ty, ty);
            }
            AssocItemKind::Fn(box Fn { ref sig, ref generics, ref body, .. })
                if self.in_const_trait_impl
                    || ctxt == AssocCtxt::Trait
                    || matches!(sig.header.constness, Const::Yes(_)) =>
            {
                self.visit_vis(&item.vis);
                self.visit_ident(item.ident);
                let kind = FnKind::Fn(
                    FnCtxt::Assoc(ctxt),
                    item.ident,
                    sig,
                    &item.vis,
                    generics,
                    body.as_deref(),
                );
                self.visit_fn(kind, item.span, item.id);
            }
            _ => self
                .with_in_trait_impl(false, None, |this| visit::walk_assoc_item(this, item, ctxt)),
        }
    }
}

/// When encountering an equality constraint in a `where` clause, emit an error. If the code seems
/// like it's setting an associated type, provide an appropriate suggestion.
fn deny_equality_constraints(
    this: &mut AstValidator<'_>,
    predicate: &WhereEqPredicate,
    generics: &Generics,
) {
    let mut err = this.err_handler().struct_span_err(
        predicate.span,
        "equality constraints are not yet supported in `where` clauses",
    );
    err.span_label(predicate.span, "not supported");

    // Given `<A as Foo>::Bar = RhsTy`, suggest `A: Foo<Bar = RhsTy>`.
    if let TyKind::Path(Some(qself), full_path) = &predicate.lhs_ty.kind {
        if let TyKind::Path(None, path) = &qself.ty.kind {
            match &path.segments[..] {
                [PathSegment { ident, args: None, .. }] => {
                    for param in &generics.params {
                        if param.ident == *ident {
                            let param = ident;
                            match &full_path.segments[qself.position..] {
                                [PathSegment { ident, args, .. }] => {
                                    // Make a new `Path` from `foo::Bar` to `Foo<Bar = RhsTy>`.
                                    let mut assoc_path = full_path.clone();
                                    // Remove `Bar` from `Foo::Bar`.
                                    assoc_path.segments.pop();
                                    let len = assoc_path.segments.len() - 1;
                                    let gen_args = args.as_ref().map(|p| (**p).clone());
                                    // Build `<Bar = RhsTy>`.
                                    let arg = AngleBracketedArg::Constraint(AssocConstraint {
                                        id: rustc_ast::node_id::DUMMY_NODE_ID,
                                        ident: *ident,
                                        gen_args,
                                        kind: AssocConstraintKind::Equality {
                                            term: predicate.rhs_ty.clone().into(),
                                        },
                                        span: ident.span,
                                    });
                                    // Add `<Bar = RhsTy>` to `Foo`.
                                    match &mut assoc_path.segments[len].args {
                                        Some(args) => match args.deref_mut() {
                                            GenericArgs::Parenthesized(_) => continue,
                                            GenericArgs::AngleBracketed(args) => {
                                                args.args.push(arg);
                                            }
                                        },
                                        empty_args => {
                                            *empty_args = AngleBracketedArgs {
                                                span: ident.span,
                                                args: vec![arg],
                                            }
                                            .into();
                                        }
                                    }
                                    err.span_suggestion_verbose(
                                        predicate.span,
                                        &format!(
                                            "if `{}` is an associated type you're trying to set, \
                                            use the associated type binding syntax",
                                            ident
                                        ),
                                        format!(
                                            "{}: {}",
                                            param,
                                            pprust::path_to_string(&assoc_path)
                                        ),
                                        Applicability::MaybeIncorrect,
                                    );
                                }
                                _ => {}
                            };
                        }
                    }
                }
                _ => {}
            }
        }
    }
    // Given `A: Foo, A::Bar = RhsTy`, suggest `A: Foo<Bar = RhsTy>`.
    if let TyKind::Path(None, full_path) = &predicate.lhs_ty.kind {
        if let [potential_param, potential_assoc] = &full_path.segments[..] {
            for param in &generics.params {
                if param.ident == potential_param.ident {
                    for bound in &param.bounds {
                        if let ast::GenericBound::Trait(trait_ref, TraitBoundModifier::None) = bound
                        {
                            if let [trait_segment] = &trait_ref.trait_ref.path.segments[..] {
                                let assoc = pprust::path_to_string(&ast::Path::from_ident(
                                    potential_assoc.ident,
                                ));
                                let ty = pprust::ty_to_string(&predicate.rhs_ty);
                                let (args, span) = match &trait_segment.args {
                                    Some(args) => match args.deref() {
                                        ast::GenericArgs::AngleBracketed(args) => {
                                            let Some(arg) = args.args.last() else {
                                                continue;
                                            };
                                            (
                                                format!(", {} = {}", assoc, ty),
                                                arg.span().shrink_to_hi(),
                                            )
                                        }
                                        _ => continue,
                                    },
                                    None => (
                                        format!("<{} = {}>", assoc, ty),
                                        trait_segment.span().shrink_to_hi(),
                                    ),
                                };
                                err.multipart_suggestion(
                                    &format!(
                                        "if `{}::{}` is an associated type you're trying to set, \
                                        use the associated type binding syntax",
                                        trait_segment.ident, potential_assoc.ident,
                                    ),
                                    vec![(span, args), (predicate.span, String::new())],
                                    Applicability::MaybeIncorrect,
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    err.note(
        "see issue #20041 <https://github.com/rust-lang/rust/issues/20041> for more information",
    );
    err.emit();
}

pub fn check_crate(session: &Session, krate: &Crate, lints: &mut LintBuffer) -> bool {
    let mut validator = AstValidator {
        session,
        extern_mod: None,
        in_trait_impl: false,
        in_const_trait_impl: false,
        has_proc_macro_decls: false,
        outer_impl_trait: None,
        disallow_tilde_const: None,
        is_impl_trait_banned: false,
        is_assoc_ty_bound_banned: false,
        forbidden_let_reason: Some(ForbiddenLetReason::GenericForbidden),
        lint_buffer: lints,
    };
    visit::walk_crate(&mut validator, krate);

    validator.has_proc_macro_decls
}

/// Used to forbid `let` expressions in certain syntactic locations.
#[derive(Clone, Copy, Subdiagnostic)]
pub(crate) enum ForbiddenLetReason {
    /// `let` is not valid and the source environment is not important
    GenericForbidden,
    /// A let chain with the `||` operator
    #[note(not_supported_or)]
    NotSupportedOr(#[primary_span] Span),
    /// A let chain with invalid parentheses
    ///
    /// For example, `let 1 = 1 && (expr && expr)` is allowed
    /// but `(let 1 = 1 && (let 1 = 1 && (let 1 = 1))) && let a = 1` is not
    #[note(not_supported_parentheses)]
    NotSupportedParentheses(#[primary_span] Span),
}
