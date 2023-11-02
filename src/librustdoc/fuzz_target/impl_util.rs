use crate::clean::Function;
use crate::clean::GenericParamDefKind;
use crate::clean::Visibility;
use crate::clean::WherePredicate;
use crate::clean::{self, ItemKind, Struct};
use crate::clean::{
    GenericArg, GenericArgs, GenericBound, Generics, Impl, ImplKind, Item, Lifetime, Path, Type,
};
use crate::error::Error;
use crate::formats;
use crate::formats::cache::Cache;
use crate::formats::item_type::ItemType;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_function::ApiUnsafety;
use crate::fuzz_target::api_graph::ApiGraph;
use crate::fuzz_target::api_util::get_type_name_from_did;
use crate::fuzz_target::api_util::is_external_type;
use crate::fuzz_target::api_util::is_generic_type;
use crate::fuzz_target::api_util::is_support_type;
use crate::fuzz_target::api_util::print_path_segment_with_args;
use crate::fuzz_target::api_util::replace_type_with;
use crate::fuzz_target::api_util::{self, is_unsupported_fuzzable, replace_lifetime};
use crate::fuzz_target::api_util::{_type_name, replace_type_lifetime};
use crate::fuzz_target::fuzzable_type::fuzzable_call_type;
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::prelude_type;
use crate::fuzz_target::statistic;
use crate::fuzz_target::trait_impl::TraitImpl;
use crate::html::format::join_with_double_colon;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::CtorKind;
use rustc_hir::def_id::DefId;
use rustc_span::Symbol;

use super::api_util::print_path_segment;
#[derive(Debug, Clone)]
pub(crate) struct FullNameMap {
    pub(crate) map: FxHashMap<DefId, (String, ItemType)>,
    pub(crate) structs: FxHashMap<DefId, Struct>,
}

impl FullNameMap {
    pub(crate) fn new() -> Self {
        FullNameMap { map: FxHashMap::default(), structs: FxHashMap::default() }
    }

    pub(crate) fn push_mapping(&mut self, def_id: DefId, full_name: &String, item_type: ItemType) {
        self.map.insert(def_id.clone(), (full_name.clone(), item_type));
    }

    pub(crate) fn get_full_name(&self, def_id: DefId) -> Option<&String> {
        match self.map.get(&def_id) {
            None => None,
            Some((full_name, _)) => Some(full_name),
        }
    }
}

fn is_prelude_api(name: &str) -> bool {
    match name {
        "fn <std::vec::Vec::<u8, std::alloc::Global> as std::convert::From::<&str>>::from(&str) -> std::vec::Vec::<u8, std::alloc::Global>"
        | "fn std::collections::hash_map::DefaultHasher::new() -> std::collections::hash_map::DefaultHasher"
        | "fn <std::string::String as std::convert::From::<&str>>::from(&str) -> std::string::String" => {
            true
        }
        _ => false,
    }
}

pub(crate) fn extract_full_name_from_cache(
    full_name_map: &mut FullNameMap,
    mut api_graph: &mut ApiGraph<'_>,
) {
    // let _trait_impl_maps = &api_graph.cache().implementors;
    let mut available_type_set = FxHashSet::<DefId>::default();

    //construct the map of `did to type`

    let paths = &api_graph.cache().paths;
    for (did, (syms, item_type)) in paths {
        let full_name = join_with_double_colon(&syms);
        full_name_map.push_mapping(*did, &full_name, *item_type);
    }

    let extertal_paths = &api_graph.cache().external_paths;
    for (did, (syms, item_type)) in extertal_paths {
        let full_name = join_with_double_colon(&syms);
        full_name_map.push_mapping(*did, &full_name, *item_type);
    }

    api_graph.set_full_name_map(&full_name_map);
}

pub(crate) fn analyse_impls(mut api_graph: &mut ApiGraph<'_>) {
    let impls = api_graph.cache().impls.clone();
    // TODO: ??
    let mut available_type_set = FxHashSet::<DefId>::default();

    let paths = &api_graph.cache().paths;
    for (did, (syms, item_type)) in paths {
        available_type_set.insert(*did);
    }

    let extertal_paths = &api_graph.cache().external_paths;
    for (did, (syms, item_type)) in extertal_paths {
        let full_name = join_with_double_colon(&syms);
        if prelude_type::is_preluded_type(&full_name) {
            available_type_set.insert(*did);
        }
    }

    //首先提取所有type的impl
    for (did, impls) in impls.iter() {
        // fetch all trait information
        for impl_ in impls {
            extract_trait_impl(impl_, &mut api_graph);
        }

        //只添加可以在full_name_map中找到对应的did的type API
        /* if available_type_set.get(&did).is_none() {
            continue;
        } */
        for impl_ in impls {
            //println!("full_name = {:?}", full_name_map._get_full_name(did).unwrap());
            analyse_impl(impl_, &mut api_graph);
        }
    }
}

fn is_prelude_trait(trait_: &Path) -> bool {
    return false;
}

fn is_ignored_trait(trait_full_name: &str) -> bool {
    if trait_full_name.starts_with("core::iter::traits::"){
        return true;
    }
    if trait_full_name.starts_with("core::fmt::") {
        return true;
    }
    match trait_full_name {
        "core::fmt::Debug"
        | "core::fmt::Display"
        | "core::clone::Clone"
        | "core::ops::drop::Drop"  => true,
        _ => false,
    }
}

fn extract_trait_impl(impl_: &formats::Impl, api_graph: &mut ApiGraph<'_>) {
    let impl_did = impl_.def_id();
    let impl_ = impl_.inner_impl();
    let blanket_type = match impl_.kind {
        ImplKind::Blanket(ref type_) => Some(*type_.clone()),
        _ => None,
    };

    if let Some(ty_did) = impl_.for_.def_id(api_graph.cache()) {
        // add type map
        // id => type
        // api_graph.add_type(ty_did, impl_for.clone());
        if let Some(ref trait_path) = impl_.trait_ {
            let mut generic_map = GenericParamMap::new();
            generic_map.add_generics(&impl_.generics);
            let trait_impl = TraitImpl::new(
                trait_path.clone(),
                impl_.for_.clone(),
                blanket_type,
                generic_map,
                impl_did,
            );
            api_graph.trait_impl_map.add_type_trait_impl(ty_did, trait_impl);
            //api_graph.add_type_trait(ty_did, trait_did);
        }
    }
}
///
/// There are multiple situations of impl statements.
///
/// No Trait: impl xx {}
///
/// Trait:
/// ```
/// impl Trait for Type
/// impl Trait for Trait
/// impl<T:bounds> Trait for T // blanket implement
/// ```
pub(crate) fn analyse_impl(impl_: &formats::Impl, api_graph: &mut ApiGraph<'_>) {
    let full_name_map = &api_graph.full_name_map;
    let tcx = api_graph.tcx();

    let impl_did = impl_.def_id();
    let impl_ = impl_.inner_impl();
    let inner_items = &impl_.items;

    //BUG FIX: TRAIT作为全限定名只能用于输入类型中带有self type的情况，这样可以推测self type，否则需要用具体的类型名
    let trait_full_name = match &impl_.trait_ {
        None => None,
        Some(trait_) => {
            //println!("{:?}", trait_);
            let trait_ty_def_id = trait_.def_id();
            let trait_full_name = full_name_map.get_full_name(trait_ty_def_id);
            if let Some(trait_name) = trait_full_name { Some(trait_name.clone()) } else { None }
        }
    };
    let is_trait_impl = impl_.trait_.is_some();
    let is_crate_trait_impl = impl_.trait_.as_ref().map_or(false, |path| path.def_id().is_local());
    let self_generics = impl_.for_.generics();
    let impl_for_def_id = impl_.for_.def_id(api_graph.cache());

    let type_full_name = if let Some(def_id) = impl_for_def_id {
        Some(api_graph.get_full_path_from_def_id(def_id))
    } else {
        None
    };

    if is_trait_impl {
        statistic::inc("TRAIT_IMPLS");
    }

    // print some debug info
    println!("\n>>>>> IMPL BLOCK INFO <<<<<");
    // println!("process impl: {:?}", impl_);
    if impl_.for_.is_full_generic() || impl_.for_.is_impl_trait() {
        println!("for type is full generic");
    }
    println!("self generics: {:?}", self_generics);
    println!("impl generics: {:?}", impl_.generics);
    println!(
        "impl trait: {}",
        impl_
            .trait_
            .as_ref()
            .map_or("none".to_string(), |path| api_graph.get_full_path_from_def_id(path.def_id()))
            .as_str()
    );
    println!("impl for: {:?}", impl_.for_);
    println!("is trait(local): {}({})", is_trait_impl, is_crate_trait_impl);
    println!("trait kind: {:?}", impl_.kind);
    println!("trait_full_name: {:?}", trait_full_name);
    println!("type_full_name: {:?}", type_full_name);
    println!("type_def_id: {:?}", impl_for_def_id);
    println!("trait_def_id: {:?}", impl_.trait_.as_ref().map(|tr| tr.def_id()));
    println!("impl_def_id: {:?}", impl_did);
    println!("is_local_impl: {}", impl_did.is_local());

    // filter some Impl
    if impl_for_def_id.is_none() {
        println!("ignore this impl for pure generic");
        return;
    }
    println!("is_external_type: {}", is_external_type(impl_for_def_id.unwrap(), api_graph.cache()));
    println!(
        "type_name: {:?}",
        get_type_name_from_did(impl_for_def_id.unwrap(), api_graph.cache())
    );

    // We extract information for two types of APIs:
    // 1. APIs implemented in target library. The Self type of API can be internal or external type. Some trait implement such as Debug will be ignored.
    // 2. Auxiliary APIs. This represent mainly the constructor APIs in std library. Such as Vec::new, String::from, etc.
    // We ignore by rule 1, we process rule 2 in analyse_impl_inner_item
    if !is_external_type(impl_for_def_id.unwrap(), api_graph.cache()) && !impl_did.is_local() {
        println!("ignore this impl for external impl");
        return;
    }

    if let Some(ref full_name) = trait_full_name {
        if is_ignored_trait(full_name) {
            println!("ignore this impl for ignore trait");
            return;
        }
    }

    let mut self_type = impl_.for_.clone();
    replace_type_lifetime(&mut self_type);

    if is_support_type(&self_type) && !is_generic_type(&self_type) {
        api_graph.type_context.borrow_mut().add_trait_type(&self_type);
    }

    if fuzzable_call_type(&self_type, &api_graph.full_name_map, api_graph.cache()).is_fuzzable()
        && !is_unsupported_fuzzable(&self_type, &api_graph.full_name_map, api_graph.cache())
    {
        println!("{} is fuzzable", _type_name(&self_type, Some(api_graph.cache())));
        api_graph.type_context.borrow_mut().add_canonical_types(&self_type, api_graph.cache());
    } else {
        println!("{} is not fuzzable", _type_name(&self_type, Some(api_graph.cache())));
    }

    let mut assoc_items = FxHashMap::<String, Type>::default();
    for item in inner_items {
        if let ItemKind::AssocTypeItem(ref typedef, _) = *item.kind {
            let name = item.name.unwrap().to_string();
            assoc_items.insert(name, typedef.type_.clone());
            /* match typedef.item_type {
                Some(ref ty) => {
                    assoc_items.insert(name, ty.clone());
                }
                None => unreachable!("unknown"),
            } */
        }
    }

    println!("assoc types:");
    for (k, v) in assoc_items.iter() {
        println!("{}: {}", k, _type_name(v, Some(api_graph.cache())));
    }

    let mut implemented = FxHashSet::<Symbol>::default();
    for item in inner_items {
        if let Some(name) = item.name {
            implemented.insert(name);
        }
        analyse_impl_inner_item(api_graph, impl_, item, &assoc_items, impl_did.is_local());
    }
    if is_trait_impl {
        let trait_ =
            api_graph.cache().traits.get(&impl_.trait_.as_ref().unwrap().def_id()).unwrap().clone();
        println!(
            "Add {} Provide Method. is_local={}",
            _type_name(
                &Type::Path { path: impl_.trait_.as_ref().unwrap().clone() },
                Some(api_graph.cache())
            ),
            trait_.def_id.is_local()
        );
        for item in trait_.items.iter() {
            if let Some(ref name) = item.name {
                if implemented.get(name).is_none() {
                    println!("[Impl] add default impl: {}", name.as_str());
                    analyse_impl_inner_item(
                        api_graph,
                        impl_,
                        item,
                        &assoc_items,
                        trait_.def_id.is_local(),
                    );
                    // analyse_impl_inner_item(api_graph, impl_, item, &assoc_items, impl_did.is_local() && is_crate_trait_impl);
                }
            }
        }
    }
    println!(">>>>>>>>>>       <<<<<<<<<<\n");
}

pub(crate) fn analyse_impl_inner_item(
    api_graph: &mut ApiGraph<'_>,
    impl_: &Impl,
    item: &Item,
    assoc_items: &FxHashMap<String, Type>,
    is_local_impl: bool,
) {
    let full_name_map = &api_graph.full_name_map;
    let is_trait_impl = impl_.trait_.is_some();
    let is_crate_trait_impl = impl_.trait_.as_ref().map_or(false, |path| path.def_id().is_local());
    let self_generics = impl_.for_.generics();
    let impl_for_def_id = impl_.for_.def_id(api_graph.cache());
    let trait_full_name = impl_
        .trait_
        .as_ref()
        .and_then(|trait_| full_name_map.get_full_name(trait_.def_id()).map(|x| x.clone()));

    let type_full_name = get_type_name_from_did(impl_for_def_id.unwrap(), api_graph.cache());

    match &*item.kind {
        ItemKind::FunctionItem(_function) => {
            unreachable!("function in impl statement");
        }
        ItemKind::MethodItem(function, _) => {
            if (is_trait_impl) {
                if (matches!(impl_.kind, clean::ImplKind::Normal)) {
                    statistic::inc("TRAIT_IMPLS");
                } else if (impl_.kind.is_blanket()) {
                    // FIXME: this might be inprecise, as the some blanket implemation might implement to multiple type
                    // BLANKET IMPLS => impl<T> trait for T
                    statistic::inc("BLANKET_IMPLS")
                }
            }

            /* println!("==== MethodItem ====");
            println!("{:?}", item);
            println!("func: {:?}", function);
            println!("===================="); */

            let clean::FnDecl { inputs, output, .. } = &function.decl;
            let mut inputs = api_util::extract_input_types(&inputs);
            let mut output = api_util::extract_output_type(&output);
            let input_len = inputs.len();
            let mut self_type = impl_.for_.clone();
            replace_type_lifetime(&mut self_type);
            let mut replace_self = |type_: &mut Type| -> bool {
                if type_.is_self_type() {
                    *type_ = self_type.clone();
                    return false;
                }
                true
            };
            let mut replace_self_assoc = |type_: &mut Type| -> bool {
                if let Type::QPath(qpathdata) = type_ {
                    if qpathdata.self_type.is_self_type() {
                        let name = print_path_segment(&qpathdata.assoc);
                        *type_ = assoc_items.get(&name).expect(&format!("{} is unfounded",name)).clone();
                    }
                    return false;
                }
                true
            };

            // let mut contains_self_type = false;
            for ty_ in inputs.iter_mut() {
                replace_type_with(ty_, &mut replace_self);
                // replace_type_with(ty_, &mut replace_self_assoc);
            }

            // let mut contains_self_output = false;
            if let Some(ref mut ty_) = output {
                replace_type_with(ty_, &mut replace_self);
                // replace_type_with(ty_, &mut replace_self_assoc);
            }

            let mut method_name = String::new();

            let api_unsafety = ApiUnsafety::_get_unsafety_from_fnheader(
                &item.fn_header(api_graph.tcx().clone()).unwrap(),
            );

            // this different from method_name for re-export item

            let api_function = ApiFunction {
                name: item.name.as_ref().unwrap().to_string(),
                full_path: type_full_name.unwrap(),
                trait_: impl_.trait_.clone().map(|path| {
                    let mut ty = Type::Path { path };
                    replace_type_lifetime(&mut ty);
                    ty
                }),
                self_: Some(self_type.clone()),
                inputs,
                output,
                _unsafe_tag: api_unsafety,
                mono: false,
                local: is_local_impl,
            };

            // if this is a external implement, only accept specific constructor function
            if !is_local_impl {
                print!("{:?} ", api_function._pretty_print(api_graph.cache()));
                if !is_prelude_api(&api_function._pretty_print(api_graph.cache())) {
                    print!("is filtered.\n");
                    return;
                } else {
                    print!("is added.\n");
                }
            }

            if !function.generics.is_empty() || !impl_.generics.is_empty() || api_function.has_impl_trait(){
                // function is a generic function
                let mut generic_function = GenericFunction::from(api_function);
                generic_function.add_generics(&function.generics);
                generic_function.add_generics(&impl_.generics);
                generic_function.set_self_type(&self_type);

                if generic_function.generic_map.is_empty() {
                    api_graph.add_api_function(generic_function.api_function);
                } else {
                    api_graph.generic_functions.push(generic_function);
                }
            } else {
                api_graph.add_api_function(api_function);
            }
        }
        _ => {
            println!("not covered item {:?}", &item);
        }
    }
}

pub(crate) fn analyse_type(item: &Item, api_graph: &mut ApiGraph<'_>) {
    //
    let did = item.item_id.expect_def_id();
    match *item.kind {
        ItemKind::StructItem(ref struct_) => {
            println!("analyse struct: {:?}", item);
            println!("analyse struct: {:?}", item.kind);

            for param in struct_.generics.params.iter() {
                match param.kind {
                    GenericParamDefKind::Lifetime { .. } => {}
                    _ => {
                        return;
                    }
                }
            }

            for field in struct_.fields.iter() {
                if let Visibility::Restricted(_) = field.visibility {
                    return;
                }
            }

            api_graph.full_name_map.structs.insert(did, struct_.clone());
        }
        ItemKind::EnumItem(ref enum_) => {}
        _ => {
            unreachable!("unexpected type: {:?}", item);
        }
    }
}
