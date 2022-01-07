use rustc_hir as hir;
use rustc_hir::Node;
use rustc_index::vec::Idx;
use rustc_middle::mir::{self, ClearCrossCrate, Local, LocalInfo, Location};
use rustc_middle::mir::{Mutability, Place, PlaceRef, ProjectionElem};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::source_map::DesugaringKind;
use rustc_span::symbol::kw;
use rustc_span::Span;

use crate::borrow_check::diagnostics::BorrowedContentSource;
use crate::borrow_check::MirBorrowckCtxt;
use crate::util::collect_writes::FindAssignments;
use rustc_errors::{Applicability, DiagnosticBuilder};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum AccessKind {
    MutableBorrow,
    Mutate,
}

impl<'a, 'tcx> MirBorrowckCtxt<'a, 'tcx> {
    pub(crate) fn report_mutability_error(
        &mut self,
        access_place: Place<'tcx>,
        span: Span,
        the_place_err: PlaceRef<'tcx>,
        error_access: AccessKind,
        location: Location,
    ) {
        debug!(
            "report_mutability_error(\
                access_place={:?}, span={:?}, the_place_err={:?}, error_access={:?}, location={:?},\
            )",
            access_place, span, the_place_err, error_access, location,
        );

        let mut err;
        let item_msg;
        let reason;
        let mut opt_source = None;
        let access_place_desc = self.describe_place(access_place.as_ref());
        debug!("report_mutability_error: access_place_desc={:?}", access_place_desc);

        match the_place_err {
            PlaceRef { local, projection: [] } => {
                item_msg = format!("`{}`", access_place_desc.unwrap());
                if access_place.as_local().is_some() {
                    reason = ", as it is not declared as mutable".to_string();
                } else {
                    let name = self.local_names[local].expect("immutable unnamed local");
                    reason = format!(", as `{}` is not declared as mutable", name);
                }
            }

            PlaceRef {
                local,
                projection: [proj_base @ .., ProjectionElem::Field(upvar_index, _)],
            } => {
                debug_assert!(is_closure_or_generator(
                    Place::ty_from(local, proj_base, self.body, self.infcx.tcx).ty
                ));

                item_msg = format!("`{}`", access_place_desc.unwrap());
                if self.is_upvar_field_projection(access_place.as_ref()).is_some() {
                    reason = ", as it is not declared as mutable".to_string();
                } else {
                    let name = self.upvars[upvar_index.index()].name;
                    reason = format!(", as `{}` is not declared as mutable", name);
                }
            }

            PlaceRef { local, projection: [ProjectionElem::Deref] }
                if self.body.local_decls[local].is_ref_for_guard() =>
            {
                item_msg = format!("`{}`", access_place_desc.unwrap());
                reason = ", as it is immutable for the pattern guard".to_string();
            }
            PlaceRef { local, projection: [ProjectionElem::Deref] }
                if self.body.local_decls[local].is_ref_to_static() =>
            {
                if access_place.projection.len() == 1 {
                    item_msg = format!("immutable static item `{}`", access_place_desc.unwrap());
                    reason = String::new();
                } else {
                    item_msg = format!("`{}`", access_place_desc.unwrap());
                    let local_info = &self.body.local_decls[local].local_info;
                    if let Some(box LocalInfo::StaticRef { def_id, .. }) = *local_info {
                        let static_name = &self.infcx.tcx.item_name(def_id);
                        reason = format!(", as `{}` is an immutable static item", static_name);
                    } else {
                        bug!("is_ref_to_static return true, but not ref to static?");
                    }
                }
            }
            PlaceRef { local: _, projection: [proj_base @ .., ProjectionElem::Deref] } => {
                if the_place_err.local == Local::new(1)
                    && proj_base.is_empty()
                    && !self.upvars.is_empty()
                {
                    item_msg = format!("`{}`", access_place_desc.unwrap());
                    debug_assert!(self.body.local_decls[Local::new(1)].ty.is_region_ptr());
                    debug_assert!(is_closure_or_generator(
                        Place::ty_from(
                            the_place_err.local,
                            the_place_err.projection,
                            self.body,
                            self.infcx.tcx
                        )
                        .ty
                    ));

                    reason = if self.is_upvar_field_projection(access_place.as_ref()).is_some() {
                        ", as it is a captured variable in a `Fn` closure".to_string()
                    } else {
                        ", as `Fn` closures cannot mutate their captured variables".to_string()
                    }
                } else {
                    let source = self.borrowed_content_source(PlaceRef {
                        local: the_place_err.local,
                        projection: proj_base,
                    });
                    let pointer_type = source.describe_for_immutable_place(self.infcx.tcx);
                    opt_source = Some(source);
                    if let Some(desc) = access_place_desc {
                        item_msg = format!("`{}`", desc);
                        reason = match error_access {
                            AccessKind::Mutate => format!(" which is behind {}", pointer_type),
                            AccessKind::MutableBorrow => {
                                format!(", as it is behind {}", pointer_type)
                            }
                        }
                    } else {
                        item_msg = format!("data in {}", pointer_type);
                        reason = String::new();
                    }
                }
            }

            PlaceRef {
                local: _,
                projection:
                    [
                        ..,
                        ProjectionElem::Index(_)
                        | ProjectionElem::ConstantIndex { .. }
                        | ProjectionElem::Subslice { .. }
                        | ProjectionElem::Downcast(..),
                    ],
            } => bug!("Unexpected immutable place."),
        }

        debug!("report_mutability_error: item_msg={:?}, reason={:?}", item_msg, reason);

        // `act` and `acted_on` are strings that let us abstract over
        // the verbs used in some diagnostic messages.
        let act;
        let acted_on;

        let span = match error_access {
            AccessKind::Mutate => {
                err = self.cannot_assign(span, &(item_msg + &reason));
                act = "assign";
                acted_on = "written";
                span
            }
            AccessKind::MutableBorrow => {
                act = "borrow as mutable";
                acted_on = "borrowed as mutable";

                let borrow_spans = self.borrow_spans(span, location);
                let borrow_span = borrow_spans.args_or_use();
                err = self.cannot_borrow_path_as_mutable_because(borrow_span, &item_msg, &reason);
                borrow_spans.var_span_label(
                    &mut err,
                    format!(
                        "mutable borrow occurs due to use of {} in closure",
                        self.describe_any_place(access_place.as_ref()),
                    ),
                );
                borrow_span
            }
        };

        debug!("report_mutability_error: act={:?}, acted_on={:?}", act, acted_on);

        match the_place_err {
            // Suggest making an existing shared borrow in a struct definition a mutable borrow.
            //
            // This is applicable when we have a deref of a field access to a deref of a local -
            // something like `*((*_1).0`. The local that we get will be a reference to the
            // struct we've got a field access of (it must be a reference since there's a deref
            // after the field access).
            PlaceRef {
                local,
                projection:
                    [
                        proj_base @ ..,
                        ProjectionElem::Deref,
                        ProjectionElem::Field(field, _),
                        ProjectionElem::Deref,
                    ],
            } => {
                err.span_label(span, format!("cannot {ACT}", ACT = act));

                if let Some((span, message)) = annotate_struct_field(
                    self.infcx.tcx,
                    Place::ty_from(local, proj_base, self.body, self.infcx.tcx).ty,
                    field,
                ) {
                    err.span_suggestion(
                        span,
                        "consider changing this to be mutable",
                        message,
                        Applicability::MaybeIncorrect,
                    );
                }
            }

            // Suggest removing a `&mut` from the use of a mutable reference.
            PlaceRef { local, projection: [] }
                if {
                    self.body
                        .local_decls
                        .get(local)
                        .map(|local_decl| {
                            if let Some(box LocalInfo::User(ClearCrossCrate::Set(
                                mir::BindingForm::ImplicitSelf(kind),
                            ))) = local_decl.local_info
                            {
                                // Check if the user variable is a `&mut self` and we can therefore
                                // suggest removing the `&mut`.
                                //
                                // Deliberately fall into this case for all implicit self types,
                                // so that we don't fall in to the next case with them.
                                kind == mir::ImplicitSelfKind::MutRef
                            } else if Some(kw::SelfLower) == self.local_names[local] {
                                // Otherwise, check if the name is the self kewyord - in which case
                                // we have an explicit self. Do the same thing in this case and check
                                // for a `self: &mut Self` to suggest removing the `&mut`.
                                if let ty::Ref(_, _, hir::Mutability::Mut) = local_decl.ty.kind {
                                    true
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        })
                        .unwrap_or(false)
                } =>
            {
                err.span_label(span, format!("cannot {ACT}", ACT = act));
                err.span_label(span, "try removing `&mut` here");
            }

            // We want to suggest users use `let mut` for local (user
            // variable) mutations...
            PlaceRef { local, projection: [] }
                if self.body.local_decls[local].can_be_made_mutable() =>
            {
                // ... but it doesn't make sense to suggest it on
                // variables that are `ref x`, `ref mut x`, `&self`,
                // or `&mut self` (such variables are simply not
                // mutable).
                let local_decl = &self.body.local_decls[local];
                assert_eq!(local_decl.mutability, Mutability::Not);

                err.span_label(span, format!("cannot {ACT}", ACT = act));
                err.span_suggestion(
                    local_decl.source_info.span,
                    "consider changing this to be mutable",
                    format!("mut {}", self.local_names[local].unwrap()),
                    Applicability::MachineApplicable,
                );
            }

            // Also suggest adding mut for upvars
            PlaceRef {
                local,
                projection: [proj_base @ .., ProjectionElem::Field(upvar_index, _)],
            } => {
                debug_assert!(is_closure_or_generator(
                    Place::ty_from(local, proj_base, self.body, self.infcx.tcx).ty
                ));

                err.span_label(span, format!("cannot {ACT}", ACT = act));

                let upvar_hir_id = self.upvars[upvar_index.index()].var_hir_id;
                if let Some(Node::Binding(pat)) = self.infcx.tcx.hir().find(upvar_hir_id) {
                    if let hir::PatKind::Binding(
                        hir::BindingAnnotation::Unannotated,
                        _,
                        upvar_ident,
                        _,
                    ) = pat.kind
                    {
                        err.span_suggestion(
                            upvar_ident.span,
                            "consider changing this to be mutable",
                            format!("mut {}", upvar_ident.name),
                            Applicability::MachineApplicable,
                        );
                    }
                }
            }

            // complete hack to approximate old AST-borrowck
            // diagnostic: if the span starts with a mutable borrow of
            // a local variable, then just suggest the user remove it.
            PlaceRef { local: _, projection: [] }
                if {
                    if let Ok(snippet) = self.infcx.tcx.sess.source_map().span_to_snippet(span) {
                        snippet.starts_with("&mut ")
                    } else {
                        false
                    }
                } =>
            {
                err.span_label(span, format!("cannot {ACT}", ACT = act));
                err.span_label(span, "try removing `&mut` here");
            }

            PlaceRef { local, projection: [ProjectionElem::Deref] }
                if self.body.local_decls[local].is_ref_for_guard() =>
            {
                err.span_label(span, format!("cannot {ACT}", ACT = act));
                err.note(
                    "variables bound in patterns are immutable until the end of the pattern guard",
                );
            }

            // We want to point out when a `&` can be readily replaced
            // with an `&mut`.
            //
            // FIXME: can this case be generalized to work for an
            // arbitrary base for the projection?
            PlaceRef { local, projection: [ProjectionElem::Deref] }
                if self.body.local_decls[local].is_user_variable() =>
            {
                let local_decl = &self.body.local_decls[local];

                let (pointer_sigil, pointer_desc) = if local_decl.ty.is_region_ptr() {
                    ("&", "reference")
                } else {
                    ("*const", "pointer")
                };

                match self.local_names[local] {
                    Some(name) if !local_decl.from_compiler_desugaring() => {
                        let label = match local_decl.local_info.as_ref().unwrap() {
                            box LocalInfo::User(ClearCrossCrate::Set(
                                mir::BindingForm::ImplicitSelf(_),
                            )) => {
                                let (span, suggestion) =
                                    suggest_ampmut_self(self.infcx.tcx, local_decl);
                                Some((true, span, suggestion))
                            }

                            box LocalInfo::User(ClearCrossCrate::Set(mir::BindingForm::Var(
                                mir::VarBindingForm {
                                    binding_mode: ty::BindingMode::BindByValue(_),
                                    opt_ty_info,
                                    ..
                                },
                            ))) => {
                                // check if the RHS is from desugaring
                                let locations = self.body.find_assignments(local);
                                let opt_assignment_rhs_span = locations
                                    .first()
                                    .map(|&location| self.body.source_info(location).span);
                                let opt_desugaring_kind =
                                    opt_assignment_rhs_span.and_then(|span| span.desugaring_kind());
                                match opt_desugaring_kind {
                                    // on for loops, RHS points to the iterator part
                                    Some(DesugaringKind::ForLoop(_)) => Some((
                                        false,
                                        opt_assignment_rhs_span.unwrap(),
                                        format!(
                                            "this iterator yields `{SIGIL}` {DESC}s",
                                            SIGIL = pointer_sigil,
                                            DESC = pointer_desc
                                        ),
                                    )),
                                    // don't create labels for compiler-generated spans
                                    Some(_) => None,
                                    None => {
                                        let (span, suggestion) = suggest_ampmut(
                                            self.infcx.tcx,
                                            local_decl,
                                            opt_assignment_rhs_span,
                                            *opt_ty_info,
                                        );
                                        Some((true, span, suggestion))
                                    }
                                }
                            }

                            box LocalInfo::User(ClearCrossCrate::Set(mir::BindingForm::Var(
                                mir::VarBindingForm {
                                    binding_mode: ty::BindingMode::BindByReference(_),
                                    ..
                                },
                            ))) => {
                                let pattern_span = local_decl.source_info.span;
                                suggest_ref_mut(self.infcx.tcx, pattern_span)
                                    .map(|replacement| (true, pattern_span, replacement))
                            }

                            box LocalInfo::User(ClearCrossCrate::Clear) => {
                                bug!("saw cleared local state")
                            }

                            _ => unreachable!(),
                        };

                        match label {
                            Some((true, err_help_span, suggested_code)) => {
                                err.span_suggestion(
                                    err_help_span,
                                    &format!(
                                        "consider changing this to be a mutable {}",
                                        pointer_desc
                                    ),
                                    suggested_code,
                                    Applicability::MachineApplicable,
                                );
                            }
                            Some((false, err_label_span, message)) => {
                                err.span_label(err_label_span, &message);
                            }
                            None => {}
                        }
                        err.span_label(
                            span,
                            format!(
                                "`{NAME}` is a `{SIGIL}` {DESC}, \
                                so the data it refers to cannot be {ACTED_ON}",
                                NAME = name,
                                SIGIL = pointer_sigil,
                                DESC = pointer_desc,
                                ACTED_ON = acted_on
                            ),
                        );
                    }
                    _ => {
                        err.span_label(
                            span,
                            format!(
                                "cannot {ACT} through `{SIGIL}` {DESC}",
                                ACT = act,
                                SIGIL = pointer_sigil,
                                DESC = pointer_desc
                            ),
                        );
                    }
                }
            }

            PlaceRef {
                local,
                projection: [ProjectionElem::Deref],
                // FIXME document what is this 1 magic number about
            } if local == Local::new(1) && !self.upvars.is_empty() => {
                self.expected_fn_found_fn_mut_call(&mut err, span, act);
            }

            PlaceRef { local: _, projection: [.., ProjectionElem::Deref] } => {
                err.span_label(span, format!("cannot {ACT}", ACT = act));

                match opt_source {
                    Some(BorrowedContentSource::OverloadedDeref(ty)) => {
                        err.help(&format!(
                            "trait `DerefMut` is required to modify through a dereference, \
                                but it is not implemented for `{}`",
                            ty,
                        ));
                    }
                    Some(BorrowedContentSource::OverloadedIndex(ty)) => {
                        err.help(&format!(
                            "trait `IndexMut` is required to modify indexed content, \
                                but it is not implemented for `{}`",
                            ty,
                        ));
                    }
                    _ => (),
                }
            }

            _ => {
                err.span_label(span, format!("cannot {ACT}", ACT = act));
            }
        }

        err.buffer(&mut self.errors_buffer);
    }

    /// Targeted error when encountering an `FnMut` closure where an `Fn` closure was expected.
    fn expected_fn_found_fn_mut_call(&self, err: &mut DiagnosticBuilder<'_>, sp: Span, act: &str) {
        err.span_label(sp, format!("cannot {}", act));

        let hir = self.infcx.tcx.hir();
        let closure_id = hir.as_local_hir_id(self.mir_def_id);
        let fn_call_id = hir.get_parent_node(closure_id);
        let node = hir.get(fn_call_id);
        let item_id = hir.enclosing_body_owner(fn_call_id);
        let mut look_at_return = true;
        // If we can detect the expression to be an `fn` call where the closure was an argument,
        // we point at the `fn` definition argument...
        if let hir::Node::Expr(hir::Expr { kind: hir::ExprKind::Call(func, args), .. }) = node {
            let arg_pos = args
                .iter()
                .enumerate()
                .filter(|(_, arg)| arg.span == self.body.span)
                .map(|(pos, _)| pos)
                .next();
            let def_id = hir.local_def_id(item_id);
            let tables = self.infcx.tcx.typeck_tables_of(def_id);
            if let Some(ty::FnDef(def_id, _)) =
                tables.node_type_opt(func.hir_id).as_ref().map(|ty| &ty.kind)
            {
                let arg = match hir.get_if_local(*def_id) {
                    Some(
                        hir::Node::Item(hir::Item {
                            ident, kind: hir::ItemKind::Fn(sig, ..), ..
                        })
                        | hir::Node::TraitItem(hir::TraitItem {
                            ident,
                            kind: hir::TraitItemKind::Fn(sig, _),
                            ..
                        })
                        | hir::Node::ImplItem(hir::ImplItem {
                            ident,
                            kind: hir::ImplItemKind::Fn(sig, _),
                            ..
                        }),
                    ) => Some(
                        arg_pos
                            .and_then(|pos| {
                                sig.decl.inputs.get(
                                    pos + if sig.decl.implicit_self.has_implicit_self() {
                                        1
                                    } else {
                                        0
                                    },
                                )
                            })
                            .map(|arg| arg.span)
                            .unwrap_or(ident.span),
                    ),
                    _ => None,
                };
                if let Some(span) = arg {
                    err.span_label(span, "change this to accept `FnMut` instead of `Fn`");
                    err.span_label(func.span, "expects `Fn` instead of `FnMut`");
                    if self.infcx.tcx.sess.source_map().is_multiline(self.body.span) {
                        err.span_label(self.body.span, "in this closure");
                    }
                    look_at_return = false;
                }
            }
        }

        if look_at_return && hir.get_return_block(closure_id).is_some() {
            // ...otherwise we are probably in the tail expression of the function, point at the
            // return type.
            match hir.get(hir.get_parent_item(fn_call_id)) {
                hir::Node::Item(hir::Item { ident, kind: hir::ItemKind::Fn(sig, ..), .. })
                | hir::Node::TraitItem(hir::TraitItem {
                    ident,
                    kind: hir::TraitItemKind::Fn(sig, _),
                    ..
                })
                | hir::Node::ImplItem(hir::ImplItem {
                    ident,
                    kind: hir::ImplItemKind::Fn(sig, _),
                    ..
                }) => {
                    err.span_label(ident.span, "");
                    err.span_label(
                        sig.decl.output.span(),
                        "change this to return `FnMut` instead of `Fn`",
                    );
                    err.span_label(self.body.span, "in this closure");
                }
                _ => {}
            }
        }
    }
}

fn suggest_ampmut_self<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_decl: &mir::LocalDecl<'tcx>,
) -> (Span, String) {
    let sp = local_decl.source_info.span;
    (
        sp,
        match tcx.sess.source_map().span_to_snippet(sp) {
            Ok(snippet) => {
                let lt_pos = snippet.find('\'');
                if let Some(lt_pos) = lt_pos {
                    format!("&{}mut self", &snippet[lt_pos..snippet.len() - 4])
                } else {
                    "&mut self".to_string()
                }
            }
            _ => "&mut self".to_string(),
        },
    )
}

// When we want to suggest a user change a local variable to be a `&mut`, there
// are three potential "obvious" things to highlight:
//
// let ident [: Type] [= RightHandSideExpression];
//     ^^^^^    ^^^^     ^^^^^^^^^^^^^^^^^^^^^^^
//     (1.)     (2.)              (3.)
//
// We can always fallback on highlighting the first. But chances are good that
// the user experience will be better if we highlight one of the others if possible;
// for example, if the RHS is present and the Type is not, then the type is going to
// be inferred *from* the RHS, which means we should highlight that (and suggest
// that they borrow the RHS mutably).
//
// This implementation attempts to emulate AST-borrowck prioritization
// by trying (3.), then (2.) and finally falling back on (1.).
fn suggest_ampmut<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_decl: &mir::LocalDecl<'tcx>,
    opt_assignment_rhs_span: Option<Span>,
    opt_ty_info: Option<Span>,
) -> (Span, String) {
    if let Some(assignment_rhs_span) = opt_assignment_rhs_span {
        if let Ok(src) = tcx.sess.source_map().span_to_snippet(assignment_rhs_span) {
            if let (true, Some(ws_pos)) =
                (src.starts_with("&'"), src.find(|c: char| -> bool { c.is_whitespace() }))
            {
                let lt_name = &src[1..ws_pos];
                let ty = &src[ws_pos..];
                return (assignment_rhs_span, format!("&{} mut {}", lt_name, ty));
            } else if src.starts_with('&') {
                let borrowed_expr = &src[1..];
                return (assignment_rhs_span, format!("&mut {}", borrowed_expr));
            }
        }
    }

    let highlight_span = match opt_ty_info {
        // if this is a variable binding with an explicit type,
        // try to highlight that for the suggestion.
        Some(ty_span) => ty_span,

        // otherwise, just highlight the span associated with
        // the (MIR) LocalDecl.
        None => local_decl.source_info.span,
    };

    if let Ok(src) = tcx.sess.source_map().span_to_snippet(highlight_span) {
        if let (true, Some(ws_pos)) =
            (src.starts_with("&'"), src.find(|c: char| -> bool { c.is_whitespace() }))
        {
            let lt_name = &src[1..ws_pos];
            let ty = &src[ws_pos..];
            return (highlight_span, format!("&{} mut{}", lt_name, ty));
        }
    }

    let ty_mut = local_decl.ty.builtin_deref(true).unwrap();
    assert_eq!(ty_mut.mutbl, hir::Mutability::Not);
    (
        highlight_span,
        if local_decl.ty.is_region_ptr() {
            format!("&mut {}", ty_mut.ty)
        } else {
            format!("*mut {}", ty_mut.ty)
        },
    )
}

fn is_closure_or_generator(ty: Ty<'_>) -> bool {
    ty.is_closure() || ty.is_generator()
}

/// Adds a suggestion to a struct definition given a field access to a local.
/// This function expects the local to be a reference to a struct in order to produce a suggestion.
///
/// ```text
/// LL |     s: &'a String
///    |        ---------- use `&'a mut String` here to make mutable
/// ```
fn annotate_struct_field(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    field: &mir::Field,
) -> Option<(Span, String)> {
    // Expect our local to be a reference to a struct of some kind.
    if let ty::Ref(_, ty, _) = ty.kind {
        if let ty::Adt(def, _) = ty.kind {
            let field = def.all_fields().nth(field.index())?;
            // Use the HIR types to construct the diagnostic message.
            let hir_id = tcx.hir().as_local_hir_id(field.did.as_local()?);
            let node = tcx.hir().find(hir_id)?;
            // Now we're dealing with the actual struct that we're going to suggest a change to,
            // we can expect a field that is an immutable reference to a type.
            if let hir::Node::Field(field) = node {
                if let hir::TyKind::Rptr(
                    lifetime,
                    hir::MutTy { mutbl: hir::Mutability::Not, ref ty },
                ) = field.ty.kind
                {
                    // Get the snippets in two parts - the named lifetime (if there is one) and
                    // type being referenced, that way we can reconstruct the snippet without loss
                    // of detail.
                    let type_snippet = tcx.sess.source_map().span_to_snippet(ty.span).ok()?;
                    let lifetime_snippet = if !lifetime.is_elided() {
                        format!("{} ", tcx.sess.source_map().span_to_snippet(lifetime.span).ok()?)
                    } else {
                        String::new()
                    };

                    return Some((
                        field.ty.span,
                        format!("&{}mut {}", lifetime_snippet, &*type_snippet,),
                    ));
                }
            }
        }
    }

    None
}

/// If possible, suggest replacing `ref` with `ref mut`.
fn suggest_ref_mut(tcx: TyCtxt<'_>, binding_span: Span) -> Option<String> {
    let hi_src = tcx.sess.source_map().span_to_snippet(binding_span).ok()?;
    if hi_src.starts_with("ref") && hi_src["ref".len()..].starts_with(rustc_lexer::is_whitespace) {
        let replacement = format!("ref mut{}", &hi_src["ref".len()..]);
        Some(replacement)
    } else {
        None
    }
}
