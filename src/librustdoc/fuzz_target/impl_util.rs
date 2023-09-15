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
use crate::fuzz_target::api_util::{_type_name,replace_type_lifetime};
use crate::fuzz_target::api_util::is_external_type;
use crate::fuzz_target::api_util::print_path_segment;
use crate::fuzz_target::api_util::replace_type_with;
use crate::fuzz_target::api_util::{self, is_param_self_type, replace_self_type, replace_lifetime};
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

pub(crate) fn extract_full_name_from_cache(
    full_name_map: &mut FullNameMap,
    mut api_graph: &mut ApiGraph<'_>,
) {
    let _trait_impl_maps = &api_graph.cache().implementors;
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
        if available_type_set.get(&did).is_none() {
            continue;
        }
        for impl_ in impls {
            //println!("full_name = {:?}", full_name_map._get_full_name(did).unwrap());
            analyse_impl(impl_, &mut api_graph);
        }
    }
}

fn is_prelude_trait(trait_: &Path) -> bool {
    return false;
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

    if impl_for_def_id.is_none() {
        println!("ignore this impl for pure generic");
        return;
    }

    if is_trait_impl && !is_crate_trait_impl {
        println!("ignore this external trait");
        return;
    }
    // only analyse local trait for any type, and external trait for local type
    // ignore external trait impl for external type
    if is_external_type(impl_for_def_id.unwrap(), api_graph.cache()) {
        /* if !is_trait_impl {
            println!("ignore this impl");
            return;
        } */
        // if trait neither prelude nor crate trait
        if is_trait_impl
            && !is_prelude_trait(&impl_.trait_.as_ref().unwrap())
            && !is_crate_trait_impl
        {
            println!("ignore this trait impl");
            return;
        }
    }

    if fuzzable_call_type(&impl_.for_, &api_graph.full_name_map, api_graph.cache()).is_fuzzable() {
        let mut ty=impl_.for_.clone();
        replace_type_lifetime(&mut ty);
        api_graph.type_context.borrow_mut().add_canonical_types(&ty, api_graph.cache());
    } else {
        println!("{} is not fuzzable", _type_name(&impl_.for_, Some(api_graph.cache())));
    }

    let mut assoc_items = FxHashMap::<String, Type>::default();
    for item in inner_items {
        if let ItemKind::AssocTypeItem(ref typedef, _) = *item.kind {
            let name = item.name.unwrap().to_string();
            match typedef.item_type {
                Some(ref ty) => {
                    assoc_items.insert(name, ty.clone());
                }
                None => unreachable!(),
            }
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
        analyse_impl_inner_item(api_graph, impl_, item, &assoc_items);
    }
    if is_trait_impl {
        let trait_ =
            api_graph.cache().traits.get(&impl_.trait_.as_ref().unwrap().def_id()).unwrap().clone();
        for item in trait_.items.iter() {
            if let Some(ref name) = item.name {
                if implemented.get(name).is_none() {
                    println!("[Impl] add default impl: {}", name.as_str());
                    analyse_impl_inner_item(api_graph, impl_, item, &assoc_items);
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

    /* let trait_full_name = match &impl_.trait_ {
        None => None,
        Some(trait_) => {
            //println!("{:?}", trait_);
            let trait_ty_def_id = trait_.def_id();
            let trait_full_name = full_name_map.get_full_name(trait_ty_def_id);
            if let Some(trait_name) = trait_full_name { Some(trait_name.clone()) } else { None }
        }
    }; */
    let type_full_name = if let Some(def_id) = impl_for_def_id {
        Some(api_graph.get_full_path_from_def_id(def_id))
    } else {
        None
    };
    match &*item.kind {
        ItemKind::FunctionItem(_function) => {
            unreachable!("function in impl statement");
        }
        ItemKind::MethodItem(function, _) => {
            statistic::inc("FUNCTIONS");

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
            let mut contains_self_type = false;
            let input_len = inputs.len();
            /* let mut replace_assoc_item = |type_: &Type| -> Option<Type> {
                match type_ {
                    Type::QPath(qpathdata) => {
                        let name = print_path_segment(None, &qpathdata.assoc, None);
                        Some(
                            assoc_items
                                .get(&name)
                                .expect(&format!("can not find {} from {:?}", name, assoc_items))
                                .clone(),
                        )
                    }
                    _ => None,
                }
            }; */
            

            for ty_ in inputs.iter_mut() {
                if is_param_self_type(ty_) {
                    contains_self_type = true;
                    let raplaced_ty = replace_self_type(ty_, &impl_.for_);
                    *ty_ = raplaced_ty;
                }
                
                // *ty_ = replace_type_with(ty_, &mut replace_assoc_item);
            }
            //println!("after replace, input = {:?}", inputs);
            let mut contains_self_output = false;
            if let Some(ref mut ty_) = output {
                if is_param_self_type(&ty_) {
                    let replaced_type = replace_self_type(&ty_, &impl_.for_);
                    contains_self_output = true;
                    *ty_ = replaced_type
                }

                // *ty_ = replace_type_with(ty_, &mut replace_assoc_item);
            }

            let mut method_name = String::new();
            //使用全限定名称：type::f
            //如果函数输入参数中含有self type，则使用trait name（也可以使用type name）
            //如果函数输入参数中不含有self type，则使用type name
            let method_type_name = if contains_self_type {
                if let Some(ref trait_name) = trait_full_name {
                    trait_name.clone()
                } else if let Some(ref type_name) = type_full_name {
                    type_name.clone()
                } else {
                    //println!("trait not in current crate.");
                    //println!("type not in current crate.");
                    return;
                }
            } else {
                if let Some(ref type_name) = type_full_name {
                    type_name.clone()
                } else {
                    //println!("type not in current crate.");
                    return;
                }
            };
            method_name.push_str(method_type_name.as_str());
            method_name.push_str("::");
            method_name.push_str(item.name.as_ref().unwrap().as_str());
            //println!("method name in impl:{:?}", method_name);

            let api_unsafety = ApiUnsafety::_get_unsafety_from_fnheader(
                &item.fn_header(api_graph.tcx().clone()).unwrap(),
            );

            let local = match impl_for_def_id {
                Some(did) => !is_external_type(did, api_graph.cache()),
                None => is_crate_trait_impl, // if type is generic, judge by trait
            };

            //生成api function
            //如果是实现了trait的话，需要把trait的全路径也包括进去
            /* match &impl_.trait_ {
                None => None,
                Some(_) => {
                    if let Some(ref real_trait_name) = trait_full_name {
                        Some(real_trait_name.clone())
                    } else {
                        //println!("Trait not found in current crate.");
                        return;
                    }
                }
            }; */

            let api_function = ApiFunction {
                full_name: method_name,
                inputs,
                output,
                _trait_full_path: trait_full_name,
                _unsafe_tag: api_unsafety,
                mono: false,
                local,
            };

            let type_generics = if let Some(ref did) = impl_for_def_id {
                api_graph.type_generics.get(did).map(|x| x.clone()).unwrap_or_default()
            } else {
                Generics::default()
            };

            if !function.generics.is_empty()
                || !impl_.generics.is_empty()
                || (contains_self_type && !type_generics.is_empty())
            {
                // function is a generic function
                let mut generic_function = GenericFunction::from(api_function);
                generic_function.add_generics(&function.generics);
                generic_function.add_generics(&impl_.generics);
                // generic_function.add_generics(&type_generics);
                // generic_function.resolve_bounded_symbol();
                // if there is no generic, regard it as a normal function
                if generic_function.generic_map.is_empty() {
                    api_graph.add_api_function(generic_function.api_function);
                } else {
                    if generic_function.api_function.is_local() {
                        statistic::inc("GENERIC_FUNCTIONS");
                    }
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
            if let CtorKind::Fictive = struct_.struct_type {
                for field in struct_.fields.iter() {
                    if let Visibility::Restricted(_) = field.visibility {
                        return;
                    }
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
/*
pub(crate) fn analyse_trait(api_graph: &mut ApiGraph<'_>) {
    let cache = api_graph.cache();
    for (did, trait_) in cache.traits.iter() {
        println!("trait!: {did:?} {trait_:?}");
        for item in trait_.items.iter() {
            println!("{:?}", item);
            println!("{:?}", item.kind);
        }
    }
}
 */
