//! The Rust AST Visitor. Extracts useful information and massages it into a form
//! usable for `clean`.

use rustc_ast::ast;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_hir::Node;
use rustc_middle::middle::privacy::AccessLevel;
use rustc_middle::ty::TyCtxt;
use rustc_span::hygiene::MacroKind;
use rustc_span::source_map::Spanned;
use rustc_span::symbol::{kw, sym, Ident, Symbol};
use rustc_span::{self, Span};

use std::mem;

use crate::clean::{self, AttributesExt, NestedAttributesExt};
use crate::core;
use crate::doctree::*;

// FIXME: Should this be replaced with tcx.def_path_str?
fn def_id_to_path(tcx: TyCtxt<'_>, did: DefId) -> Vec<String> {
    let crate_name = tcx.crate_name(did.krate).to_string();
    let relative = tcx.def_path(did).data.into_iter().filter_map(|elem| {
        // extern blocks have an empty name
        let s = elem.data.to_string();
        if !s.is_empty() { Some(s) } else { None }
    });
    std::iter::once(crate_name).chain(relative).collect()
}

// Also, is there some reason that this doesn't use the 'visit'
// framework from syntax?.

pub struct RustdocVisitor<'a, 'tcx> {
    cx: &'a mut core::DocContext<'tcx>,
    view_item_stack: FxHashSet<hir::HirId>,
    inlining: bool,
    /// Are the current module and all of its parents public?
    inside_public_path: bool,
    exact_paths: FxHashMap<DefId, Vec<String>>,
}

impl<'a, 'tcx> RustdocVisitor<'a, 'tcx> {
    pub fn new(cx: &'a mut core::DocContext<'tcx>) -> RustdocVisitor<'a, 'tcx> {
        // If the root is re-exported, terminate all recursion.
        let mut stack = FxHashSet::default();
        stack.insert(hir::CRATE_HIR_ID);
        RustdocVisitor {
            cx,
            view_item_stack: stack,
            inlining: false,
            inside_public_path: true,
            exact_paths: FxHashMap::default(),
        }
    }

    fn store_path(&mut self, did: DefId) {
        let tcx = self.cx.tcx;
        self.exact_paths.entry(did).or_insert_with(|| def_id_to_path(tcx, did));
    }

    pub fn visit(mut self, krate: &'tcx hir::Crate<'_>) -> Module<'tcx> {
        let mut module = self.visit_mod_contents(
            krate.item.span,
            krate.item.attrs,
            &Spanned { span: rustc_span::DUMMY_SP, node: hir::VisibilityKind::Public },
            hir::CRATE_HIR_ID,
            &krate.item.module,
            None,
        );
        // Attach the crate's exported macros to the top-level module:
        module
            .macros
            .extend(krate.exported_macros.iter().map(|def| self.visit_local_macro(def, None)));
        module.is_crate = true;

        self.cx.renderinfo.get_mut().exact_paths = self.exact_paths;

        module
    }

    fn visit_variant_data(
        &mut self,
        item: &'tcx hir::Item<'_>,
        name: Symbol,
        sd: &'tcx hir::VariantData<'_>,
        generics: &'tcx hir::Generics<'_>,
    ) -> Struct<'tcx> {
        debug!("visiting struct");
        let struct_type = struct_type_from_def(&*sd);
        Struct {
            id: item.hir_id,
            struct_type,
            name,
            vis: &item.vis,
            attrs: &item.attrs,
            generics,
            fields: sd.fields(),
            whence: item.span,
        }
    }

    fn visit_union_data(
        &mut self,
        item: &'tcx hir::Item<'_>,
        name: Symbol,
        sd: &'tcx hir::VariantData<'_>,
        generics: &'tcx hir::Generics<'_>,
    ) -> Union<'tcx> {
        debug!("visiting union");
        let struct_type = struct_type_from_def(&*sd);
        Union {
            id: item.hir_id,
            struct_type,
            name,
            vis: &item.vis,
            attrs: &item.attrs,
            generics,
            fields: sd.fields(),
            whence: item.span,
        }
    }

    fn visit_enum_def(
        &mut self,
        it: &'tcx hir::Item<'_>,
        name: Symbol,
        def: &'tcx hir::EnumDef<'_>,
        generics: &'tcx hir::Generics<'_>,
    ) -> Enum<'tcx> {
        debug!("visiting enum");
        Enum {
            name,
            variants: def
                .variants
                .iter()
                .map(|v| Variant {
                    name: v.ident.name,
                    id: v.id,
                    attrs: &v.attrs,
                    def: &v.data,
                    whence: v.span,
                })
                .collect(),
            vis: &it.vis,
            generics,
            attrs: &it.attrs,
            id: it.hir_id,
            whence: it.span,
        }
    }

    fn visit_fn(
        &mut self,
        om: &mut Module<'tcx>,
        item: &'tcx hir::Item<'_>,
        name: Symbol,
        decl: &'tcx hir::FnDecl<'_>,
        header: hir::FnHeader,
        generics: &'tcx hir::Generics<'_>,
        body: hir::BodyId,
    ) {
        debug!("visiting fn");
        let macro_kind = item.attrs.iter().find_map(|a| {
            if a.check_name(sym::proc_macro) {
                Some(MacroKind::Bang)
            } else if a.check_name(sym::proc_macro_derive) {
                Some(MacroKind::Derive)
            } else if a.check_name(sym::proc_macro_attribute) {
                Some(MacroKind::Attr)
            } else {
                None
            }
        });
        match macro_kind {
            Some(kind) => {
                let name = if kind == MacroKind::Derive {
                    item.attrs
                        .lists(sym::proc_macro_derive)
                        .find_map(|mi| mi.ident())
                        .expect("proc-macro derives require a name")
                        .name
                } else {
                    name
                };

                let mut helpers = Vec::new();
                for mi in item.attrs.lists(sym::proc_macro_derive) {
                    if !mi.check_name(sym::attributes) {
                        continue;
                    }

                    if let Some(list) = mi.meta_item_list() {
                        for inner_mi in list {
                            if let Some(ident) = inner_mi.ident() {
                                helpers.push(ident.name);
                            }
                        }
                    }
                }

                om.proc_macros.push(ProcMacro {
                    name,
                    id: item.hir_id,
                    kind,
                    helpers,
                    attrs: &item.attrs,
                    whence: item.span,
                });
            }
            None => {
                om.fns.push(Function {
                    id: item.hir_id,
                    vis: &item.vis,
                    attrs: &item.attrs,
                    decl,
                    name,
                    whence: item.span,
                    generics,
                    header,
                    body,
                });
            }
        }
    }

    fn visit_mod_contents(
        &mut self,
        span: Span,
        attrs: &'tcx [ast::Attribute],
        vis: &'tcx hir::Visibility<'_>,
        id: hir::HirId,
        m: &'tcx hir::Mod<'tcx>,
        name: Option<Symbol>,
    ) -> Module<'tcx> {
        let mut om = Module::new(name, attrs, vis);
        om.where_outer = span;
        om.where_inner = m.inner;
        om.id = id;
        // Keep track of if there were any private modules in the path.
        let orig_inside_public_path = self.inside_public_path;
        self.inside_public_path &= vis.node.is_pub();
        for i in m.item_ids {
            let item = self.cx.tcx.hir().expect_item(i.id);
            self.visit_item(item, None, &mut om);
        }
        self.inside_public_path = orig_inside_public_path;
        om
    }

    /// Tries to resolve the target of a `pub use` statement and inlines the
    /// target if it is defined locally and would not be documented otherwise,
    /// or when it is specifically requested with `please_inline`.
    /// (the latter is the case when the import is marked `doc(inline)`)
    ///
    /// Cross-crate inlining occurs later on during crate cleaning
    /// and follows different rules.
    ///
    /// Returns `true` if the target has been inlined.
    fn maybe_inline_local(
        &mut self,
        id: hir::HirId,
        res: Res,
        renamed: Option<Ident>,
        glob: bool,
        om: &mut Module<'tcx>,
        please_inline: bool,
    ) -> bool {
        fn inherits_doc_hidden(cx: &core::DocContext<'_>, mut node: hir::HirId) -> bool {
            while let Some(id) = cx.tcx.hir().get_enclosing_scope(node) {
                node = id;
                if cx.tcx.hir().attrs(node).lists(sym::doc).has_word(sym::hidden) {
                    return true;
                }
                if node == hir::CRATE_HIR_ID {
                    break;
                }
            }
            false
        }

        debug!("maybe_inline_local res: {:?}", res);

        let tcx = self.cx.tcx;
        let res_did = if let Some(did) = res.opt_def_id() {
            did
        } else {
            return false;
        };

        let use_attrs = tcx.hir().attrs(id);
        // Don't inline `doc(hidden)` imports so they can be stripped at a later stage.
        let is_no_inline = use_attrs.lists(sym::doc).has_word(sym::no_inline)
            || use_attrs.lists(sym::doc).has_word(sym::hidden);

        // For cross-crate impl inlining we need to know whether items are
        // reachable in documentation -- a previously nonreachable item can be
        // made reachable by cross-crate inlining which we're checking here.
        // (this is done here because we need to know this upfront).
        if !res_did.is_local() && !is_no_inline {
            let attrs = clean::inline::load_attrs(self.cx, res_did);
            let self_is_hidden = attrs.lists(sym::doc).has_word(sym::hidden);
            match res {
                Res::Def(
                    DefKind::Trait
                    | DefKind::Struct
                    | DefKind::Union
                    | DefKind::Enum
                    | DefKind::ForeignTy
                    | DefKind::TyAlias,
                    did,
                ) if !self_is_hidden => {
                    self.cx.renderinfo.get_mut().access_levels.map.insert(did, AccessLevel::Public);
                }
                Res::Def(DefKind::Mod, did) => {
                    if !self_is_hidden {
                        crate::visit_lib::LibEmbargoVisitor::new(self.cx).visit_mod(did);
                    }
                }
                _ => {}
            }

            return false;
        }

        let res_hir_id = match res_did.as_local() {
            Some(n) => tcx.hir().as_local_hir_id(n),
            None => return false,
        };

        let is_private = !self.cx.renderinfo.borrow().access_levels.is_public(res_did);
        let is_hidden = inherits_doc_hidden(self.cx, res_hir_id);

        // Only inline if requested or if the item would otherwise be stripped.
        if (!please_inline && !is_private && !is_hidden) || is_no_inline {
            return false;
        }

        if !self.view_item_stack.insert(res_hir_id) {
            return false;
        }

        let ret = match tcx.hir().get(res_hir_id) {
            Node::Item(&hir::Item { kind: hir::ItemKind::Mod(ref m), .. }) if glob => {
                let prev = mem::replace(&mut self.inlining, true);
                for i in m.item_ids {
                    let i = self.cx.tcx.hir().expect_item(i.id);
                    self.visit_item(i, None, om);
                }
                self.inlining = prev;
                true
            }
            Node::Item(it) if !glob => {
                let prev = mem::replace(&mut self.inlining, true);
                self.visit_item(it, renamed, om);
                self.inlining = prev;
                true
            }
            Node::ForeignItem(it) if !glob => {
                let prev = mem::replace(&mut self.inlining, true);
                self.visit_foreign_item(it, renamed, om);
                self.inlining = prev;
                true
            }
            Node::MacroDef(def) if !glob => {
                om.macros.push(self.visit_local_macro(def, renamed.map(|i| i.name)));
                true
            }
            _ => false,
        };
        self.view_item_stack.remove(&res_hir_id);
        ret
    }

    fn visit_item(
        &mut self,
        item: &'tcx hir::Item<'_>,
        renamed: Option<Ident>,
        om: &mut Module<'tcx>,
    ) {
        debug!("visiting item {:?}", item);
        let ident = renamed.unwrap_or(item.ident);

        if item.vis.node.is_pub() {
            let def_id = self.cx.tcx.hir().local_def_id(item.hir_id);
            self.store_path(def_id.to_def_id());
        }

        match item.kind {
            hir::ItemKind::ForeignMod(ref fm) => {
                for item in fm.items {
                    self.visit_foreign_item(item, None, om);
                }
            }
            // If we're inlining, skip private items.
            _ if self.inlining && !item.vis.node.is_pub() => {}
            hir::ItemKind::GlobalAsm(..) => {}
            hir::ItemKind::ExternCrate(orig_name) => {
                let def_id = self.cx.tcx.hir().local_def_id(item.hir_id);
                om.extern_crates.push(ExternCrate {
                    cnum: self.cx.tcx.extern_mod_stmt_cnum(def_id).unwrap_or(LOCAL_CRATE),
                    name: ident.name,
                    path: orig_name.map(|x| x.to_string()),
                    vis: &item.vis,
                    attrs: &item.attrs,
                    whence: item.span,
                })
            }
            hir::ItemKind::Use(_, hir::UseKind::ListStem) => {}
            hir::ItemKind::Use(ref path, kind) => {
                let is_glob = kind == hir::UseKind::Glob;

                // Struct and variant constructors and proc macro stubs always show up alongside
                // their definitions, we've already processed them so just discard these.
                if let Res::Def(DefKind::Ctor(..), _) | Res::SelfCtor(..) = path.res {
                    return;
                }

                // If there was a private module in the current path then don't bother inlining
                // anything as it will probably be stripped anyway.
                if item.vis.node.is_pub() && self.inside_public_path {
                    let please_inline = item.attrs.iter().any(|item| match item.meta_item_list() {
                        Some(ref list) if item.check_name(sym::doc) => {
                            list.iter().any(|i| i.check_name(sym::inline))
                        }
                        _ => false,
                    });
                    let ident = if is_glob { None } else { Some(ident) };
                    if self.maybe_inline_local(
                        item.hir_id,
                        path.res,
                        ident,
                        is_glob,
                        om,
                        please_inline,
                    ) {
                        return;
                    }
                }

                om.imports.push(Import {
                    name: ident.name,
                    id: item.hir_id,
                    vis: &item.vis,
                    attrs: &item.attrs,
                    path,
                    glob: is_glob,
                    whence: item.span,
                });
            }
            hir::ItemKind::Mod(ref m) => {
                om.mods.push(self.visit_mod_contents(
                    item.span,
                    &item.attrs,
                    &item.vis,
                    item.hir_id,
                    m,
                    Some(ident.name),
                ));
            }
            hir::ItemKind::Enum(ref ed, ref gen) => {
                om.enums.push(self.visit_enum_def(item, ident.name, ed, gen))
            }
            hir::ItemKind::Struct(ref sd, ref gen) => {
                om.structs.push(self.visit_variant_data(item, ident.name, sd, gen))
            }
            hir::ItemKind::Union(ref sd, ref gen) => {
                om.unions.push(self.visit_union_data(item, ident.name, sd, gen))
            }
            hir::ItemKind::Fn(ref sig, ref gen, body) => {
                self.visit_fn(om, item, ident.name, &sig.decl, sig.header, gen, body)
            }
            hir::ItemKind::TyAlias(ty, ref gen) => {
                let t = Typedef {
                    ty,
                    gen,
                    name: ident.name,
                    id: item.hir_id,
                    attrs: &item.attrs,
                    whence: item.span,
                    vis: &item.vis,
                };
                om.typedefs.push(t);
            }
            hir::ItemKind::OpaqueTy(ref opaque_ty) => {
                let t = OpaqueTy {
                    opaque_ty,
                    name: ident.name,
                    id: item.hir_id,
                    attrs: &item.attrs,
                    whence: item.span,
                    vis: &item.vis,
                };
                om.opaque_tys.push(t);
            }
            hir::ItemKind::Static(type_, mutability, expr) => {
                let s = Static {
                    type_,
                    mutability,
                    expr,
                    id: item.hir_id,
                    name: ident.name,
                    attrs: &item.attrs,
                    whence: item.span,
                    vis: &item.vis,
                };
                om.statics.push(s);
            }
            hir::ItemKind::Const(type_, expr) => {
                // Underscore constants do not correspond to a nameable item and
                // so are never useful in documentation.
                if ident.name != kw::Underscore {
                    let s = Constant {
                        type_,
                        expr,
                        id: item.hir_id,
                        name: ident.name,
                        attrs: &item.attrs,
                        whence: item.span,
                        vis: &item.vis,
                    };
                    om.constants.push(s);
                }
            }
            hir::ItemKind::Trait(is_auto, unsafety, ref generics, ref bounds, ref item_ids) => {
                let items = item_ids.iter().map(|ti| self.cx.tcx.hir().trait_item(ti.id)).collect();
                let t = Trait {
                    is_auto,
                    unsafety,
                    name: ident.name,
                    items,
                    generics,
                    bounds,
                    id: item.hir_id,
                    attrs: &item.attrs,
                    whence: item.span,
                    vis: &item.vis,
                };
                om.traits.push(t);
            }
            hir::ItemKind::TraitAlias(ref generics, ref bounds) => {
                let t = TraitAlias {
                    name: ident.name,
                    generics,
                    bounds,
                    id: item.hir_id,
                    attrs: &item.attrs,
                    whence: item.span,
                    vis: &item.vis,
                };
                om.trait_aliases.push(t);
            }

            hir::ItemKind::Impl {
                unsafety,
                polarity,
                defaultness,
                constness,
                defaultness_span: _,
                ref generics,
                ref of_trait,
                self_ty,
                ref items,
            } => {
                // Don't duplicate impls when inlining or if it's implementing a trait, we'll pick
                // them up regardless of where they're located.
                if !self.inlining && of_trait.is_none() {
                    let items =
                        items.iter().map(|item| self.cx.tcx.hir().impl_item(item.id)).collect();
                    let i = Impl {
                        unsafety,
                        polarity,
                        defaultness,
                        constness,
                        generics,
                        trait_: of_trait,
                        for_: self_ty,
                        items,
                        attrs: &item.attrs,
                        id: item.hir_id,
                        whence: item.span,
                        vis: &item.vis,
                    };
                    om.impls.push(i);
                }
            }
        }
    }

    fn visit_foreign_item(
        &mut self,
        item: &'tcx hir::ForeignItem<'_>,
        renamed: Option<Ident>,
        om: &mut Module<'tcx>,
    ) {
        // If inlining we only want to include public functions.
        if self.inlining && !item.vis.node.is_pub() {
            return;
        }

        om.foreigns.push(ForeignItem {
            id: item.hir_id,
            name: renamed.unwrap_or(item.ident).name,
            kind: &item.kind,
            vis: &item.vis,
            attrs: &item.attrs,
            whence: item.span,
        });
    }

    // Convert each `exported_macro` into a doc item.
    fn visit_local_macro(
        &self,
        def: &'tcx hir::MacroDef<'_>,
        renamed: Option<Symbol>,
    ) -> Macro<'tcx> {
        debug!("visit_local_macro: {}", def.ident);
        let tts = def.ast.body.inner_tokens().trees().collect::<Vec<_>>();
        // Extract the spans of all matchers. They represent the "interface" of the macro.
        let matchers = tts.chunks(4).map(|arm| arm[0].span()).collect();

        Macro {
            hid: def.hir_id,
            def_id: self.cx.tcx.hir().local_def_id(def.hir_id).to_def_id(),
            attrs: &def.attrs,
            name: renamed.unwrap_or(def.ident.name),
            whence: def.span,
            matchers,
            imported_from: None,
        }
    }
}
