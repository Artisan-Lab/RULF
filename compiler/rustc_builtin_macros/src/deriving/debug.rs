use crate::deriving::generic::ty::*;
use crate::deriving::generic::*;
use crate::deriving::path_std;

use rustc_ast::{self as ast, MetaItem};
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::symbol::{sym, Ident, Symbol};
use rustc_span::Span;

pub fn expand_deriving_debug(
    cx: &mut ExtCtxt<'_>,
    span: Span,
    mitem: &MetaItem,
    item: &Annotatable,
    push: &mut dyn FnMut(Annotatable),
) {
    // &mut ::std::fmt::Formatter
    let fmtr = Ref(Box::new(Path(path_std!(fmt::Formatter))), ast::Mutability::Mut);

    let trait_def = TraitDef {
        span,
        path: path_std!(fmt::Debug),
        skip_path_as_bound: false,
        additional_bounds: Vec::new(),
        generics: Bounds::empty(),
        supports_unions: false,
        methods: vec![MethodDef {
            name: sym::fmt,
            generics: Bounds::empty(),
            explicit_self: true,
            nonself_args: vec![(fmtr, sym::f)],
            ret_ty: Path(path_std!(fmt::Result)),
            attributes: ast::AttrVec::new(),
            unify_fieldless_variants: false,
            combine_substructure: combine_substructure(Box::new(|a, b, c| {
                show_substructure(a, b, c)
            })),
        }],
        associated_types: Vec::new(),
    };
    trait_def.expand(cx, mitem, item, push)
}

fn show_substructure(cx: &mut ExtCtxt<'_>, span: Span, substr: &Substructure<'_>) -> BlockOrExpr {
    let (ident, vdata, fields) = match substr.fields {
        Struct(vdata, fields) => (substr.type_ident, *vdata, fields),
        EnumMatching(_, _, v, fields) => (v.ident, &v.data, fields),
        EnumTag(..) | StaticStruct(..) | StaticEnum(..) => {
            cx.span_bug(span, "nonsensical .fields in `#[derive(Debug)]`")
        }
    };

    // We want to make sure we have the ctxt set so that we can use unstable methods
    let span = cx.with_def_site_ctxt(span);
    let name = cx.expr_str(span, ident.name);
    let fmt = substr.nonselflike_args[0].clone();

    // Struct and tuples are similar enough that we use the same code for both,
    // with some extra pieces for structs due to the field names.
    let (is_struct, args_per_field) = match vdata {
        ast::VariantData::Unit(..) => {
            // Special fast path for unit variants.
            assert!(fields.is_empty());
            (false, 0)
        }
        ast::VariantData::Tuple(..) => (false, 1),
        ast::VariantData::Struct(..) => (true, 2),
    };

    // The number of fields that can be handled without an array.
    const CUTOFF: usize = 5;

    if fields.is_empty() {
        // Special case for no fields.
        let fn_path_write_str = cx.std_path(&[sym::fmt, sym::Formatter, sym::write_str]);
        let expr = cx.expr_call_global(span, fn_path_write_str, vec![fmt, name]);
        BlockOrExpr::new_expr(expr)
    } else if fields.len() <= CUTOFF {
        // Few enough fields that we can use a specific-length method.
        let debug = if is_struct {
            format!("debug_struct_field{}_finish", fields.len())
        } else {
            format!("debug_tuple_field{}_finish", fields.len())
        };
        let fn_path_debug = cx.std_path(&[sym::fmt, sym::Formatter, Symbol::intern(&debug)]);

        let mut args = Vec::with_capacity(2 + fields.len() * args_per_field);
        args.extend([fmt, name]);
        for i in 0..fields.len() {
            let field = &fields[i];
            if is_struct {
                let name = cx.expr_str(field.span, field.name.unwrap().name);
                args.push(name);
            }
            // Use an extra indirection to make sure this works for unsized types.
            let field = cx.expr_addr_of(field.span, field.self_expr.clone());
            args.push(field);
        }
        let expr = cx.expr_call_global(span, fn_path_debug, args);
        BlockOrExpr::new_expr(expr)
    } else {
        // Enough fields that we must use the any-length method.
        let mut name_exprs = Vec::with_capacity(fields.len());
        let mut value_exprs = Vec::with_capacity(fields.len());

        for field in fields {
            if is_struct {
                name_exprs.push(cx.expr_str(field.span, field.name.unwrap().name));
            }

            // Use an extra indirection to make sure this works for unsized types.
            let field = cx.expr_addr_of(field.span, field.self_expr.clone());
            value_exprs.push(field);
        }

        // `let names: &'static _ = &["field1", "field2"];`
        let names_let = if is_struct {
            let lt_static = Some(cx.lifetime_static(span));
            let ty_static_ref =
                cx.ty_rptr(span, cx.ty_infer(span), lt_static, ast::Mutability::Not);
            Some(cx.stmt_let_ty(
                span,
                false,
                Ident::new(sym::names, span),
                Some(ty_static_ref),
                cx.expr_array_ref(span, name_exprs),
            ))
        } else {
            None
        };

        // `let values: &[&dyn Debug] = &[&&self.field1, &&self.field2];`
        let path_debug = cx.path_global(span, cx.std_path(&[sym::fmt, sym::Debug]));
        let ty_dyn_debug = cx.ty(
            span,
            ast::TyKind::TraitObject(vec![cx.trait_bound(path_debug)], ast::TraitObjectSyntax::Dyn),
        );
        let ty_slice = cx.ty(
            span,
            ast::TyKind::Slice(cx.ty_rptr(span, ty_dyn_debug, None, ast::Mutability::Not)),
        );
        let values_let = cx.stmt_let_ty(
            span,
            false,
            Ident::new(sym::values, span),
            Some(cx.ty_rptr(span, ty_slice, None, ast::Mutability::Not)),
            cx.expr_array_ref(span, value_exprs),
        );

        // `fmt::Formatter::debug_struct_fields_finish(fmt, name, names, values)` or
        // `fmt::Formatter::debug_tuple_fields_finish(fmt, name, values)`
        let sym_debug = if is_struct {
            sym::debug_struct_fields_finish
        } else {
            sym::debug_tuple_fields_finish
        };
        let fn_path_debug_internal = cx.std_path(&[sym::fmt, sym::Formatter, sym_debug]);

        let mut args = Vec::with_capacity(4);
        args.push(fmt);
        args.push(name);
        if is_struct {
            args.push(cx.expr_ident(span, Ident::new(sym::names, span)));
        }
        args.push(cx.expr_ident(span, Ident::new(sym::values, span)));
        let expr = cx.expr_call_global(span, fn_path_debug_internal, args);

        let mut stmts = Vec::with_capacity(3);
        if is_struct {
            stmts.push(names_let.unwrap());
        }
        stmts.push(values_let);
        BlockOrExpr::new_mixed(stmts, Some(expr))
    }
}
