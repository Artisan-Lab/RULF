use hir::GenericParamKind;
use rustc_errors::{
    fluent, AddToDiagnostic, Applicability, Diagnostic, DiagnosticMessage, DiagnosticStyledString,
    MultiSpan, SubdiagnosticMessage,
};
use rustc_hir as hir;
use rustc_hir::{FnRetTy, Ty};
use rustc_macros::{Diagnostic, Subdiagnostic};
use rustc_middle::ty::{Region, TyCtxt};
use rustc_span::symbol::kw;
use rustc_span::{symbol::Ident, BytePos, Span};

use crate::infer::error_reporting::{
    need_type_info::{GeneratorKindAsDiagArg, UnderspecifiedArgKind},
    ObligationCauseAsDiagArg,
};

pub mod note_and_explain;

#[derive(Diagnostic)]
#[diag(infer_opaque_hidden_type)]
pub struct OpaqueHiddenTypeDiag {
    #[primary_span]
    #[label]
    pub span: Span,
    #[note(opaque_type)]
    pub opaque_type: Span,
    #[note(hidden_type)]
    pub hidden_type: Span,
}

#[derive(Diagnostic)]
#[diag(infer_type_annotations_needed, code = "E0282")]
pub struct AnnotationRequired<'a> {
    #[primary_span]
    pub span: Span,
    pub source_kind: &'static str,
    pub source_name: &'a str,
    #[label]
    pub failure_span: Option<Span>,
    #[subdiagnostic]
    pub bad_label: Option<InferenceBadError<'a>>,
    #[subdiagnostic]
    pub infer_subdiags: Vec<SourceKindSubdiag<'a>>,
    #[subdiagnostic]
    pub multi_suggestions: Vec<SourceKindMultiSuggestion<'a>>,
}

// Copy of `AnnotationRequired` for E0283
#[derive(Diagnostic)]
#[diag(infer_type_annotations_needed, code = "E0283")]
pub struct AmbigousImpl<'a> {
    #[primary_span]
    pub span: Span,
    pub source_kind: &'static str,
    pub source_name: &'a str,
    #[label]
    pub failure_span: Option<Span>,
    #[subdiagnostic]
    pub bad_label: Option<InferenceBadError<'a>>,
    #[subdiagnostic]
    pub infer_subdiags: Vec<SourceKindSubdiag<'a>>,
    #[subdiagnostic]
    pub multi_suggestions: Vec<SourceKindMultiSuggestion<'a>>,
}

// Copy of `AnnotationRequired` for E0284
#[derive(Diagnostic)]
#[diag(infer_type_annotations_needed, code = "E0284")]
pub struct AmbigousReturn<'a> {
    #[primary_span]
    pub span: Span,
    pub source_kind: &'static str,
    pub source_name: &'a str,
    #[label]
    pub failure_span: Option<Span>,
    #[subdiagnostic]
    pub bad_label: Option<InferenceBadError<'a>>,
    #[subdiagnostic]
    pub infer_subdiags: Vec<SourceKindSubdiag<'a>>,
    #[subdiagnostic]
    pub multi_suggestions: Vec<SourceKindMultiSuggestion<'a>>,
}

#[derive(Diagnostic)]
#[diag(infer_need_type_info_in_generator, code = "E0698")]
pub struct NeedTypeInfoInGenerator<'a> {
    #[primary_span]
    pub span: Span,
    pub generator_kind: GeneratorKindAsDiagArg,
    #[subdiagnostic]
    pub bad_label: InferenceBadError<'a>,
}

// Used when a better one isn't available
#[derive(Subdiagnostic)]
#[label(infer_label_bad)]
pub struct InferenceBadError<'a> {
    #[primary_span]
    pub span: Span,
    pub bad_kind: &'static str,
    pub prefix_kind: UnderspecifiedArgKind,
    pub has_parent: bool,
    pub prefix: &'a str,
    pub parent_prefix: &'a str,
    pub parent_name: String,
    pub name: String,
}

#[derive(Subdiagnostic)]
pub enum SourceKindSubdiag<'a> {
    #[suggestion_verbose(
        infer_source_kind_subdiag_let,
        code = ": {type_name}",
        applicability = "has-placeholders"
    )]
    LetLike {
        #[primary_span]
        span: Span,
        name: String,
        type_name: String,
        kind: &'static str,
        x_kind: &'static str,
        prefix_kind: UnderspecifiedArgKind,
        prefix: &'a str,
        arg_name: String,
    },
    #[label(infer_source_kind_subdiag_generic_label)]
    GenericLabel {
        #[primary_span]
        span: Span,
        is_type: bool,
        param_name: String,
        parent_exists: bool,
        parent_prefix: String,
        parent_name: String,
    },
    #[suggestion_verbose(
        infer_source_kind_subdiag_generic_suggestion,
        code = "::<{args}>",
        applicability = "has-placeholders"
    )]
    GenericSuggestion {
        #[primary_span]
        span: Span,
        arg_count: usize,
        args: String,
    },
}

#[derive(Subdiagnostic)]
pub enum SourceKindMultiSuggestion<'a> {
    #[multipart_suggestion_verbose(
        infer_source_kind_fully_qualified,
        applicability = "has-placeholders"
    )]
    FullyQualified {
        #[suggestion_part(code = "{def_path}({adjustment}")]
        span_lo: Span,
        #[suggestion_part(code = "{successor_pos}")]
        span_hi: Span,
        def_path: String,
        adjustment: &'a str,
        successor_pos: &'a str,
    },
    #[multipart_suggestion_verbose(
        infer_source_kind_closure_return,
        applicability = "has-placeholders"
    )]
    ClosureReturn {
        #[suggestion_part(code = "{start_span_code}")]
        start_span: Span,
        start_span_code: String,
        #[suggestion_part(code = " }}")]
        end_span: Option<Span>,
    },
}

impl<'a> SourceKindMultiSuggestion<'a> {
    pub fn new_fully_qualified(
        span: Span,
        def_path: String,
        adjustment: &'a str,
        successor: (&'a str, BytePos),
    ) -> Self {
        Self::FullyQualified {
            span_lo: span.shrink_to_lo(),
            span_hi: span.shrink_to_hi().with_hi(successor.1),
            def_path,
            adjustment,
            successor_pos: successor.0,
        }
    }

    pub fn new_closure_return(
        ty_info: String,
        data: &'a FnRetTy<'a>,
        should_wrap_expr: Option<Span>,
    ) -> Self {
        let (arrow, post) = match data {
            FnRetTy::DefaultReturn(_) => ("-> ", " "),
            _ => ("", ""),
        };
        let (start_span, start_span_code, end_span) = match should_wrap_expr {
            Some(end_span) => {
                (data.span(), format!("{}{}{}{{ ", arrow, ty_info, post), Some(end_span))
            }
            None => (data.span(), format!("{}{}{}", arrow, ty_info, post), None),
        };
        Self::ClosureReturn { start_span, start_span_code, end_span }
    }
}

pub enum RegionOriginNote<'a> {
    Plain {
        span: Span,
        msg: DiagnosticMessage,
    },
    WithName {
        span: Span,
        msg: DiagnosticMessage,
        name: &'a str,
        continues: bool,
    },
    WithRequirement {
        span: Span,
        requirement: ObligationCauseAsDiagArg<'a>,
        expected_found: Option<(DiagnosticStyledString, DiagnosticStyledString)>,
    },
}

impl AddToDiagnostic for RegionOriginNote<'_> {
    fn add_to_diagnostic_with<F>(self, diag: &mut Diagnostic, _: F)
    where
        F: Fn(&mut Diagnostic, SubdiagnosticMessage) -> SubdiagnosticMessage,
    {
        let mut label_or_note = |span, msg: DiagnosticMessage| {
            let sub_count = diag.children.iter().filter(|d| d.span.is_dummy()).count();
            let expanded_sub_count = diag.children.iter().filter(|d| !d.span.is_dummy()).count();
            let span_is_primary = diag.span.primary_spans().iter().all(|&sp| sp == span);
            if span_is_primary && sub_count == 0 && expanded_sub_count == 0 {
                diag.span_label(span, msg);
            } else if span_is_primary && expanded_sub_count == 0 {
                diag.note(msg);
            } else {
                diag.span_note(span, msg);
            }
        };
        match self {
            RegionOriginNote::Plain { span, msg } => {
                label_or_note(span, msg);
            }
            RegionOriginNote::WithName { span, msg, name, continues } => {
                label_or_note(span, msg);
                diag.set_arg("name", name);
                diag.set_arg("continues", continues);
            }
            RegionOriginNote::WithRequirement {
                span,
                requirement,
                expected_found: Some((expected, found)),
            } => {
                label_or_note(span, fluent::infer_subtype);
                diag.set_arg("requirement", requirement);

                diag.note_expected_found(&"", expected, &"", found);
            }
            RegionOriginNote::WithRequirement { span, requirement, expected_found: None } => {
                // FIXME: this really should be handled at some earlier stage. Our
                // handling of region checking when type errors are present is
                // *terrible*.
                label_or_note(span, fluent::infer_subtype_2);
                diag.set_arg("requirement", requirement);
            }
        };
    }
}

pub enum LifetimeMismatchLabels {
    InRet {
        param_span: Span,
        ret_span: Span,
        span: Span,
        label_var1: Option<Ident>,
    },
    Normal {
        hir_equal: bool,
        ty_sup: Span,
        ty_sub: Span,
        span: Span,
        sup: Option<Ident>,
        sub: Option<Ident>,
    },
}

impl AddToDiagnostic for LifetimeMismatchLabels {
    fn add_to_diagnostic_with<F>(self, diag: &mut Diagnostic, _: F)
    where
        F: Fn(&mut Diagnostic, SubdiagnosticMessage) -> SubdiagnosticMessage,
    {
        match self {
            LifetimeMismatchLabels::InRet { param_span, ret_span, span, label_var1 } => {
                diag.span_label(param_span, fluent::infer_declared_different);
                diag.span_label(ret_span, fluent::infer_nothing);
                diag.span_label(span, fluent::infer_data_returned);
                diag.set_arg("label_var1_exists", label_var1.is_some());
                diag.set_arg("label_var1", label_var1.map(|x| x.to_string()).unwrap_or_default());
            }
            LifetimeMismatchLabels::Normal {
                hir_equal,
                ty_sup,
                ty_sub,
                span,
                sup: label_var1,
                sub: label_var2,
            } => {
                if hir_equal {
                    diag.span_label(ty_sup, fluent::infer_declared_multiple);
                    diag.span_label(ty_sub, fluent::infer_nothing);
                    diag.span_label(span, fluent::infer_data_lifetime_flow);
                } else {
                    diag.span_label(ty_sup, fluent::infer_types_declared_different);
                    diag.span_label(ty_sub, fluent::infer_nothing);
                    diag.span_label(span, fluent::infer_data_flows);
                    diag.set_arg("label_var1_exists", label_var1.is_some());
                    diag.set_arg(
                        "label_var1",
                        label_var1.map(|x| x.to_string()).unwrap_or_default(),
                    );
                    diag.set_arg("label_var2_exists", label_var2.is_some());
                    diag.set_arg(
                        "label_var2",
                        label_var2.map(|x| x.to_string()).unwrap_or_default(),
                    );
                }
            }
        }
    }
}

pub struct AddLifetimeParamsSuggestion<'a> {
    pub tcx: TyCtxt<'a>,
    pub sub: Region<'a>,
    pub ty_sup: &'a Ty<'a>,
    pub ty_sub: &'a Ty<'a>,
    pub add_note: bool,
}

impl AddToDiagnostic for AddLifetimeParamsSuggestion<'_> {
    fn add_to_diagnostic_with<F>(self, diag: &mut Diagnostic, _: F)
    where
        F: Fn(&mut Diagnostic, SubdiagnosticMessage) -> SubdiagnosticMessage,
    {
        let mut mk_suggestion = || {
            let (
                hir::Ty { kind: hir::TyKind::Rptr(lifetime_sub, _), .. },
                hir::Ty { kind: hir::TyKind::Rptr(lifetime_sup, _), .. },
            ) = (self.ty_sub, self.ty_sup) else {
                return false;
            };

            if !lifetime_sub.name.is_anonymous() || !lifetime_sup.name.is_anonymous() {
                return false;
            };

            let Some(anon_reg) = self.tcx.is_suitable_region(self.sub) else {
                return false;
            };

            let hir_id = self.tcx.hir().local_def_id_to_hir_id(anon_reg.def_id);

            let node = self.tcx.hir().get(hir_id);
            let is_impl = matches!(&node, hir::Node::ImplItem(_));
            let generics = match node {
                hir::Node::Item(&hir::Item {
                    kind: hir::ItemKind::Fn(_, ref generics, ..),
                    ..
                })
                | hir::Node::TraitItem(&hir::TraitItem { ref generics, .. })
                | hir::Node::ImplItem(&hir::ImplItem { ref generics, .. }) => generics,
                _ => return false,
            };

            let suggestion_param_name = generics
                .params
                .iter()
                .filter(|p| matches!(p.kind, GenericParamKind::Lifetime { .. }))
                .map(|p| p.name.ident().name)
                .find(|i| *i != kw::UnderscoreLifetime);
            let introduce_new = suggestion_param_name.is_none();
            let suggestion_param_name =
                suggestion_param_name.map(|n| n.to_string()).unwrap_or_else(|| "'a".to_owned());

            debug!(?lifetime_sup.span);
            debug!(?lifetime_sub.span);
            let make_suggestion = |span: rustc_span::Span| {
                if span.is_empty() {
                    (span, format!("{}, ", suggestion_param_name))
                } else if let Ok("&") = self.tcx.sess.source_map().span_to_snippet(span).as_deref()
                {
                    (span.shrink_to_hi(), format!("{} ", suggestion_param_name))
                } else {
                    (span, suggestion_param_name.clone())
                }
            };
            let mut suggestions =
                vec![make_suggestion(lifetime_sub.span), make_suggestion(lifetime_sup.span)];

            if introduce_new {
                let new_param_suggestion = if let Some(first) =
                    generics.params.iter().find(|p| !p.name.ident().span.is_empty())
                {
                    (first.span.shrink_to_lo(), format!("{}, ", suggestion_param_name))
                } else {
                    (generics.span, format!("<{}>", suggestion_param_name))
                };

                suggestions.push(new_param_suggestion);
            }

            diag.multipart_suggestion(
                fluent::infer_lifetime_param_suggestion,
                suggestions,
                Applicability::MaybeIncorrect,
            );
            diag.set_arg("is_impl", is_impl);
            true
        };
        if mk_suggestion() && self.add_note {
            diag.note(fluent::infer_lifetime_param_suggestion_elided);
        }
    }
}

#[derive(Diagnostic)]
#[diag(infer_lifetime_mismatch, code = "E0623")]
pub struct LifetimeMismatch<'a> {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub labels: LifetimeMismatchLabels,
    #[subdiagnostic]
    pub suggestion: AddLifetimeParamsSuggestion<'a>,
}

pub struct IntroducesStaticBecauseUnmetLifetimeReq {
    pub unmet_requirements: MultiSpan,
    pub binding_span: Span,
}

impl AddToDiagnostic for IntroducesStaticBecauseUnmetLifetimeReq {
    fn add_to_diagnostic_with<F>(mut self, diag: &mut Diagnostic, _: F)
    where
        F: Fn(&mut Diagnostic, SubdiagnosticMessage) -> SubdiagnosticMessage,
    {
        self.unmet_requirements
            .push_span_label(self.binding_span, fluent::infer_msl_introduces_static);
        diag.span_note(self.unmet_requirements, fluent::infer_msl_unmet_req);
    }
}

// FIXME(#100717): replace with a `Option<Span>` when subdiagnostic supports that
#[derive(Subdiagnostic)]
pub enum DoesNotOutliveStaticFromImpl {
    #[note(infer_does_not_outlive_static_from_impl)]
    Spanned {
        #[primary_span]
        span: Span,
    },
    #[note(infer_does_not_outlive_static_from_impl)]
    Unspanned,
}

#[derive(Subdiagnostic)]
pub enum ImplicitStaticLifetimeSubdiag {
    #[note(infer_implicit_static_lifetime_note)]
    Note {
        #[primary_span]
        span: Span,
    },
    #[suggestion_verbose(
        infer_implicit_static_lifetime_suggestion,
        code = " + '_",
        applicability = "maybe-incorrect"
    )]
    Sugg {
        #[primary_span]
        span: Span,
    },
}

#[derive(Diagnostic)]
#[diag(infer_mismatched_static_lifetime)]
pub struct MismatchedStaticLifetime<'a> {
    #[primary_span]
    pub cause_span: Span,
    #[subdiagnostic]
    pub unmet_lifetime_reqs: IntroducesStaticBecauseUnmetLifetimeReq,
    #[subdiagnostic]
    pub expl: Option<note_and_explain::RegionExplanation<'a>>,
    #[subdiagnostic]
    pub does_not_outlive_static_from_impl: DoesNotOutliveStaticFromImpl,
    #[subdiagnostic(eager)]
    pub implicit_static_lifetimes: Vec<ImplicitStaticLifetimeSubdiag>,
}
