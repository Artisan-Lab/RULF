use crate::clean::Function;
use crate::clean::WherePredicate;
use crate::clean::{self, ItemKind, Struct};
use crate::clean::{GenericBound, Generics, Impl, Item, Path, Type};
use crate::error::Error;
use crate::formats;
use crate::formats::cache::Cache;
use crate::formats::item_type::ItemType;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_function::ApiUnsafety;
use crate::fuzz_target::api_graph::ApiGraph;
use crate::fuzz_target::api_util::is_external_type;
use crate::fuzz_target::api_util::{self, is_param_self_type, replace_self_type};
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::prelude_type;
use crate::fuzz_target::statistic;
use crate::html::format::join_with_double_colon;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_span::Symbol;
#[derive(Debug, Clone)]
pub(crate) struct FullNameMap {
    pub(crate) map: FxHashMap<DefId, (String, ItemType)>,
}

impl FullNameMap {
    pub(crate) fn new() -> Self {
        let map = FxHashMap::default();
        FullNameMap { map }
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
    let impls_ = api_graph.cache().impls.clone();
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
    for (did, impls) in impls_ {
        //只添加可以在full_name_map中找到对应的did的type
        if available_type_set.get(&did).is_none() {
            continue;
        }
        for impl_ in &impls {
            //println!("full_name = {:?}", full_name_map._get_full_name(did).unwrap());
            analyse_impl(impl_, &mut api_graph);
        }
    }
}

fn is_prelude_trait(trait_: &Path) -> bool {
    return false;
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
    let impl_did = impl_.def_id();
    let impl_ = impl_.inner_impl();
    let inner_items = &impl_.items;
    let tcx = api_graph.tcx();
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
    let impl_for = &impl_.for_; // 
    let impl_for_def_id = impl_for.def_id(api_graph.cache());
    let type_full_name = if let Some(def_id) = impl_for_def_id {
        Some(api_graph.get_full_path_from_def_id(def_id))
    } else {
        None
    };

    // print some debug info
    println!("\n>>>>> IMPL BLOCK INFO <<<<<");
    println!("process impl: {:?}", impl_);
    if impl_for.is_full_generic() || impl_for.is_impl_trait() {
        println!("for type is generic/trait");
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
    println!("impl for: {:?}", impl_for);
    println!("is trait(local): {}({})", is_trait_impl, is_crate_trait_impl);
    println!("trait kind: {:?}", impl_.kind);
    println!("trait_full_name: {:?}", trait_full_name);
    println!("type_full_name: {:?}", type_full_name);
    println!("type_def_id: {:?}", impl_for_def_id);
    println!("trait_def_id: {:?}", impl_.trait_.as_ref().map(|tr| tr.def_id()));
    println!("impl_def_id: {:?}", impl_did);

    if let Some(ty_did) = impl_for_def_id {
        // add type map
        // id => type
        // api_graph.add_type(ty_did, impl_for.clone());
        if let Some(ref trait_path) = impl_.trait_ {
            let mut generic_map = GenericParamMap::new();
            generic_map.add_generics(&impl_.generics);
            api_graph.add_type_trait_impl(
                ty_did,
                trait_path.clone(),
                impl_for.clone(),
                generic_map,
                impl_did,
            );
            //api_graph.add_type_trait(ty_did, trait_did);
        }
    }

    if is_trait_impl && !api_util::is_generic_type(impl_for) {
        api_graph.type_context.borrow_mut().add_type_candidate(impl_for);
    }

    if (is_trait_impl && !is_crate_trait_impl && !is_prelude_trait(&impl_.trait_.as_ref().unwrap()))
        || (!is_trait_impl && !is_external_type(impl_for_def_id.unwrap(), api_graph.cache()))
    {
        println!("ignore this impl");
        return;
    }

    let mut implemented = FxHashSet::<Symbol>::default();
    for item in inner_items {
        if let Some(name) = item.name {
            implemented.insert(name);
        }
        analyse_impl_inner_item(api_graph, impl_, item);
    }
    if is_trait_impl {
        let trait_ =
            api_graph.cache().traits.get(&impl_.trait_.as_ref().unwrap().def_id()).unwrap().clone();
        for item in trait_.items.iter() {
            if item.name.is_none() {
                continue;
            }
            if implemented.get(item.name.as_ref().unwrap()).is_none() {
                analyse_impl_inner_item(api_graph, impl_, item);
            }
        }
    }
    println!(">>>>>>>>>>       <<<<<<<<<<\n");
}

pub(crate) fn analyse_impl_inner_item(api_graph: &mut ApiGraph<'_>, impl_: &Impl, item: &Item) {
    let full_name_map = &api_graph.full_name_map;
    let is_trait_impl = impl_.trait_.is_some();
    let is_crate_trait_impl = impl_.trait_.as_ref().map_or(false, |path| path.def_id().is_local());
    let self_generics = impl_.for_.generics();
    let impl_for_def_id = impl_.for_.def_id(api_graph.cache());
    let trait_full_name = match &impl_.trait_ {
        None => None,
        Some(trait_) => {
            //println!("{:?}", trait_);
            let trait_ty_def_id = trait_.def_id();
            let trait_full_name = full_name_map.get_full_name(trait_ty_def_id);
            if let Some(trait_name) = trait_full_name { Some(trait_name.clone()) } else { None }
        }
    };
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
            let output = api_util::extract_output_type(&output);
            let mut contains_self_type = false;
            let input_len = inputs.len();

            for ty_ in inputs.iter_mut() {
                if is_param_self_type(ty_) {
                    contains_self_type = true;
                    let raplaced_ty = replace_self_type(ty_, &impl_.for_);
                    *ty_ = raplaced_ty;
                }
            }
            //println!("after replace, input = {:?}", inputs);
            let mut contains_self_output = false;
            let output = match output {
                None => None,
                Some(ty_) => {
                    if is_param_self_type(&ty_) {
                        let replaced_type = replace_self_type(&ty_, &impl_.for_);
                        contains_self_output = true;
                        Some(replaced_type)
                    } else {
                        Some(ty_)
                    }
                }
            };

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
            //生成api function
            //如果是实现了trait的话，需要把trait的全路径也包括进去
            let api_function = match &impl_.trait_ {
                None => ApiFunction {
                    full_name: method_name,
                    inputs,
                    output,
                    _trait_full_path: None,
                    _unsafe_tag: api_unsafety,
                    mono: false,
                },
                Some(_) => {
                    if let Some(ref real_trait_name) = trait_full_name {
                        ApiFunction {
                            full_name: method_name,
                            inputs,
                            output,
                            _trait_full_path: Some(real_trait_name.clone()),
                            _unsafe_tag: api_unsafety,
                            mono: false,
                        }
                    } else {
                        //println!("Trait not found in current crate.");
                        return;
                    }
                }
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
                generic_function.add_generics(&type_generics);
                generic_function.resolve_bounded_symbol();
                // if there is no generic, regard it as a normal function
                if generic_function.generic_map.is_empty() {
                    api_graph.add_api_function(generic_function.api_function);
                } else {
                    api_graph.generic_functions.push(generic_function);
                    statistic::inc("GENERIC_FUNCTIONS");
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
    println!("analyse struct: {:?}", item);

    let generics = match *item.kind {
        ItemKind::StructItem(ref struct_) => {
            println!("generics: {:?}", &struct_.generics);
            struct_.generics.clone()
        }
        ItemKind::EnumItem(ref enum_) => {
            println!("generics: {:?}", &enum_.generics);
            enum_.generics.clone()
        }
        _ => {
            unreachable!("unexpected type: {:?}", item);
        }
    };

    let did = item.item_id.expect_def_id();
    api_graph.type_generics.insert(did, generics.clone());
}

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
