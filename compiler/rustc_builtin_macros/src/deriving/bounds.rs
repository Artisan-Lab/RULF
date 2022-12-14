use crate::deriving::generic::ty::*;
use crate::deriving::generic::*;
use crate::deriving::path_std;

use rustc_ast::MetaItem;
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::Span;

pub fn expand_deriving_copy(
    cx: &mut ExtCtxt<'_>,
    span: Span,
    mitem: &MetaItem,
    item: &Annotatable,
    push: &mut dyn FnMut(Annotatable),
) {
    let trait_def = TraitDef {
        span,
        path: path_std!(marker::Copy),
        skip_path_as_bound: false,
        additional_bounds: Vec::new(),
        generics: Bounds::empty(),
        supports_unions: true,
        methods: Vec::new(),
        associated_types: Vec::new(),
    };

    trait_def.expand(cx, mitem, item, push);
}
