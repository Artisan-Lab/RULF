use crate::clean::{self};
use crate::clean::{Generics, WherePredicate};
use crate::formats::cache::Cache;
use crate::formats::item_type::ItemType;
use crate::fuzz_target::api_function::{ApiFunction, ApiUnsafety};
use crate::fuzz_target::api_util;
use crate::html::format::join_with_double_colon;
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::hash::Hash;
//TODO:是否需要为impl里面的method重新设计数据结构？目前沿用了ApiFunction,或者直接对ApiFunction进行扩展
//两种函数目前相差一个defaultness
use crate::fuzz_target::api_graph::ApiGraph;
use crate::fuzz_target::prelude_type;
use crate::fuzz_target::type_util::{
    get_generics_of_clean_type, get_qpaths_in_clean_type, replace_types,
};

#[derive(Debug, Clone)]
pub(crate) struct CrateImplCollection {
    //impl type类型的impl块
    pub(crate) impl_types: Vec<clean::Impl>,
    //impl type for trait类型的impl块
    pub(crate) impl_trait_for_types: Vec<clean::Impl>,
    //TODO:带泛型参数的impl块，但self是否该视为泛型？
    pub(crate) _generic_impl: Vec<clean::Impl>,
    pub(crate) _generic_impl_for_traits: Vec<clean::Impl>,
}

impl CrateImplCollection {
    pub(crate) fn new() -> Self {
        let impl_types = Vec::new();
        let impl_trait_for_types = Vec::new();
        let _generic_impl = Vec::new();
        let _generic_impl_for_traits = Vec::new();
        CrateImplCollection {
            impl_types,
            impl_trait_for_types,
            _generic_impl,
            _generic_impl_for_traits,
        }
    }

    pub(crate) fn add_impl(&mut self, impl_: &clean::Impl) {
        //println!("impl type = {:?}", impl_.for_);
        let _impl_type = &impl_.for_;
        match impl_.trait_ {
            None => {
                self.impl_types.push(impl_.clone());
            }
            Some(ref _ty_) => {
                self.impl_trait_for_types.push(impl_.clone());
            }
        }
    }
}

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

    pub(crate) fn _get_full_name(&self, def_id: DefId) -> Option<&String> {
        match self.map.get(&def_id) {
            None => None,
            Some((full_name, _)) => Some(full_name),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TraitsOfType {
    pub map: FxHashMap<DefId, FxHashSet<clean::Type>>,
}

impl TraitsOfType {
    pub fn new() -> Self {
        TraitsOfType { map: FxHashMap::default() }
    }

    pub fn add_trait_of_type(&mut self, did: DefId, trait_: &clean::Type) {
        if self.map.contains_key(&did) {
            let old_traits = self.map.get_mut(&did).unwrap();
            old_traits.insert(trait_.to_owned());
        } else {
            let mut traits = FxHashSet::default();
            traits.insert(trait_.to_owned());
            self.map.insert(did, traits);
        }
    }
}

pub fn extract_impls_from_cache(
    cache: &Cache,
    full_name_map: &mut FullNameMap,
    traits_of_type: &mut TraitsOfType,
    mut api_graph: &mut ApiGraph<'_>,
) {
    let mut crate_impl_collection = CrateImplCollection::new();
    //construct the map of `did to type`
    for (did, (syms, item_type)) in cache.paths {
        let full_name = join_with_double_colon(&syms);
        full_name_map.push_mapping(*did, &full_name, *item_type);
    }

    for (did, (syms, item_type)) in cache.external_paths {
        let full_name = join_with_double_colon(&syms);

        if prelude_type::is_preluded_type_name(&full_name) {
            full_name_map.push_mapping(*did, &full_name, *item_type);
        }
    }

    api_graph.set_full_name_map(&full_name_map);

    // 首先提取所有type的impl
    for (did, impls) in &cache.impls {
        impls.iter().for_each(|impl_| {
            if let Some(ref trait_) = impl_.inner_impl().trait_ {
                traits_of_type.add_trait_of_type(*did, trait_);
            }
        });

        // 只添加可以在full_name_map中找到对应的did的type
        if full_name_map._get_full_name(did) != None {
            for impl_ in impls {
                crate_impl_collection.add_impl(impl_.inner_impl());
            }
        }
    }

    api_graph.set_traits_of_type(traits_of_type);
    //分析impl type类型
    for impl_ in &crate_impl_collection.impl_types {
        _analyse_impl(impl_, &full_name_map, &mut api_graph);
    }

    for impl_ in &crate_impl_collection.impl_trait_for_types {
        _analyse_impl(impl_, &full_name_map, &mut api_graph);
    }
    //TODO：如何提取trait对应的impl，impl traitA for traitB? impl dyn traitA?
}

fn full_path(paths: &Vec<String>) -> String {
    paths.join("::")
}

pub(crate) fn _analyse_impl(
    impl_: &clean::Impl,
    full_name_map: &FullNameMap,
    api_graph: &mut ApiGraph<'_>,
) {
    let inner_items = &impl_.items;
    let impl_generics = &impl_.generics;

    // check where predicate
    if where_preidicates_bounds_restrict_generic(impl_generics) {
        return;
    }

    // BUG FIX: TRAIT作为全限定名只能用于输入类型中带有self type的情况，这样可以推测self type，否则需要用具体的类型名
    let trait_full_name = impl_
        .trait_
        .as_ref()
        .map(|trait_| {
            let trait_ty_def_id = &trait_.def_id().unwrap();
            let trait_full_name = full_name_map._get_full_name(trait_ty_def_id);
            trait_full_name.map(|trait_full_name| trait_full_name.to_owned())
        })
        .flatten();

    let impl_ty_def_id = &impl_.for_.def_id(api_graph.cache());

    let type_full_name = impl_ty_def_id
        .map(|ref def_id| {
            let type_name = full_name_map._get_full_name(def_id);
            type_name.map(|real_type_name| real_type_name.to_owned())
        })
        .flatten();

    // collect associate typedefs
    let mut associate_typedefs = FxHashMap::default();
    inner_items.iter().for_each(|item| {
        if let clean::TypedefItem(typedef, ..) = &item.inner {
            if let Some(ref item_name) = item.name {
                if let Some(ref item_type) = typedef.item_type {
                    associate_typedefs.insert(item_name.to_owned(), item_type.to_owned());
                }
            }
        }
    });

    for item in inner_items {
        match &item.inner {
            //这段代码暂时没用了，impl块里面的是method item，而不是function item,暂时留着，看里面是否会出现function item
            clean::FunctionItem(_function) => {
                let function_name =
                    format!("{:?}::{:?}", type_full_name, item.name.as_ref().unwrap());
                error!("function name in impl:{:?}", function_name);
            }
            clean::MethodItem(method) => {
                let clean::FnDecl { inputs, output, .. } = method.decl.clone();
                let mut method_generics = method.generics.clone();
                let mut inputs = api_util::_extract_input_types(&inputs);
                let mut output = api_util::_extract_output_type(&output);

                // replace associate types. Replace associate type should be prior to replace self type
                // Since associate type can be `Self` type itself.
                inputs = inputs
                    .into_iter()
                    .map(|input_type| {
                        replace_self_associate_types(
                            &input_type,
                            &impl_.trait_,
                            &associate_typedefs,
                        )
                    })
                    .collect_vec();
                output = output.map(|output_type| {
                    replace_self_associate_types(&output_type, &impl_.trait_, &associate_typedefs)
                });

                // replace self type
                let input_contains_self_type =
                    inputs.iter().any(|ty_| clean_type_contains_self_type(ty_));
                let output_contains_self_type =
                    inputs.iter().any(|ty_| clean_type_contains_self_type(ty_));
                let contains_self_type = input_contains_self_type | output_contains_self_type;

                inputs = inputs
                    .into_iter()
                    .map(|ty_| {
                        if clean_type_contains_self_type(&ty_) {
                            replace_self_type(&ty_, &impl_.for_)
                        } else {
                            ty_
                        }
                    })
                    .collect();

                output = output.map(|ty_| {
                    if clean_type_contains_self_type(&ty_) {
                        replace_self_type(&ty_, &impl_.for_)
                    } else {
                        ty_
                    }
                });

                // extend method generics
                let mut generics_in_method = FxHashSet::default();
                let mut free_qpaths_in_method = FxHashSet::default();
                inputs.iter().for_each(|input_type| {
                    generics_in_method.extend(get_generics_of_clean_type(input_type));
                    free_qpaths_in_method.extend(get_qpaths_in_clean_type(input_type));
                });
                output.iter().for_each(|output_type| {
                    generics_in_method.extend(get_generics_of_clean_type(output_type));
                    free_qpaths_in_method.extend(get_qpaths_in_clean_type(output_type));
                });

                method_generics = extend_generics(
                    &method_generics,
                    &impl_generics,
                    generics_in_method,
                    free_qpaths_in_method,
                );

                // 使用全限定名称：type::f
                // 如果函数输入参数中含有self type，则优先使用trait name，如果没有的话，使用type name
                // 如果函数输入参数中不含有self type，则使用type name
                let method_type_name = if contains_self_type {
                    if let Some(ref trait_name) = trait_full_name {
                        trait_name.to_owned()
                    } else if let Some(ref type_name) = type_full_name {
                        type_name.to_owned()
                    } else {
                        // Both trait and type are not in current crate
                        // We will skip such functions
                        return;
                    }
                } else {
                    if let Some(ref type_name) = type_full_name {
                        type_name.to_owned()
                    } else {
                        // Type is not defined in current crate
                        return;
                    }
                };
                let method_name = format!("{}::{}", method_type_name, item.name.as_ref().unwrap());

                let api_unsafety = ApiUnsafety::_get_unsafety_from_fnheader(
                    &item.fn_header(api_graph.tcx().clone()).unwrap(),
                );
                //生成api function
                //如果是实现了trait的话，需要把trait的全路径也包括进去
                let api_function = match &impl_.trait_ {
                    None => ApiFunction {
                        full_name: method_name,
                        generics: method_generics,
                        inputs,
                        output,
                        _trait_full_path: None,
                        _unsafe_tag: api_unsafety,
                        return_type_notation: false,
                        is_helper: false,
                    },
                    Some(_) => {
                        if let Some(ref real_trait_name) = trait_full_name {
                            ApiFunction {
                                full_name: method_name,
                                generics: method_generics,
                                inputs,
                                output,
                                _trait_full_path: Some(real_trait_name.clone()),
                                _unsafe_tag: api_unsafety,
                                return_type_notation: false,
                                is_helper: false,
                            }
                        } else {
                            trace!("Trait not found in current crate.");
                            return;
                        }
                    }
                };
                api_graph.add_api_function(api_function);
            }
            _ => {}
        }
    }
}

/// 递归判断一个类型里面是否含有self类型，目前只考虑引用和复合类型
fn clean_type_contains_self_type(ty_: &clean::Type) -> bool {
    if ty_.is_self_type() {
        return true;
    }
    match ty_ {
        clean::Type::BorrowedRef { type_, .. } => {
            let inner_ty = &**type_;
            return clean_type_contains_self_type(inner_ty);
        }
        clean::Type::Path { path, .. } => {
            let segments = &path.segments;
            for path_segment in segments {
                let generic_args = &path_segment.args;
                match generic_args {
                    clean::GenericArgs::AngleBracketed { args, .. } => {
                        for generic_arg in args.iter() {
                            if let clean::GenericArg::Type(generic_ty) = generic_arg {
                                if clean_type_contains_self_type(generic_ty) {
                                    return true;
                                }
                            }
                        }
                    }
                    clean::GenericArgs::Parenthesized { inputs, output } => {
                        for input_type in inputs {
                            if clean_type_contains_self_type(input_type) {
                                return true;
                            }
                        }
                        if let Some(output_type) = output {
                            if clean_type_contains_self_type(output_type) {
                                return true;
                            }
                        }
                    }
                }
            }
            return false;
        }
        _ => {
            return false;
        }
    }
}

/// 将self类型替换为相应的结构体类型
fn replace_self_type(self_type: &clean::Type, impl_type: &clean::Type) -> clean::Type {
    let self_generic = clean::Type::Generic("Self".to_string());
    let mut replace_type_map = FxHashMap::default();
    replace_type_map.insert(self_generic, impl_type.to_owned());
    replace_types(self_type, &replace_type_map)
}

// Add generic param appears in `ty_` to generics. These generic should also appears in `other_generics`
fn extend_generics(
    generics: &Generics,
    other_generics: &Generics,
    generics_in_method: FxHashSet<String>,
    free_qpaths_in_method: FxHashSet<clean::Type>,
) -> Generics {
    let mut generics = generics.to_owned();
    let Generics { params: other_params, where_predicates: other_where_predicates } =
        other_generics;
    // generics can appear both in params and where_predicates
    generics_in_method.into_iter().for_each(|generic_in_type| {
        let param_def = other_params
            .iter()
            .filter(|generic_param_def| generic_param_def.name == generic_in_type)
            .map(|generic_param_def| generic_param_def.to_owned())
            .collect_vec();
        // generic_param_defs_in_type.extend(param_def);
        generics.params.extend(param_def);
        let predicate = other_where_predicates
            .iter()
            .filter(|where_predicate| {
                match where_predicate {
                    WherePredicate::BoundPredicate { ty: where_ty, .. }
                    | WherePredicate::EqPredicate { lhs: where_ty, .. } => {
                        type_is_given_generic(where_ty, &generic_in_type)
                    }
                    WherePredicate::RegionPredicate { .. } => {
                        // We current ignore lifetime bound
                        false
                    }
                }
            })
            .map(|where_predicate| where_predicate.to_owned())
            .collect_vec();
        generics.where_predicates.extend(predicate);
    });

    // free qpath can only exist in where predicate
    free_qpaths_in_method.into_iter().for_each(|free_qpath_in_method| {
        let predicate = other_where_predicates
            .iter()
            .filter(|where_predicate| {
                match where_predicate {
                    WherePredicate::BoundPredicate { ty: where_ty, .. } => {
                        *where_ty == free_qpath_in_method
                    }
                    WherePredicate::RegionPredicate { .. } | WherePredicate::EqPredicate { .. } => {
                        // We current ignore lifetime bound
                        false
                    }
                }
            })
            .map(|where_predicate| where_predicate.to_owned())
            .collect_vec();
        generics.where_predicates.extend(predicate);
    });

    // remove duplicate. Not sure whether these is essential
    remove_duplicate_in_vec(&mut generics.params);
    // remove_duplicate_in_vec(&mut generics.where_predicates);

    generics
}

/// determine clean type equals to given generic
fn type_is_given_generic(ty_: &clean::Type, given_generic: &str) -> bool {
    if let clean::Type::Generic(generic) = ty_ { generic == given_generic } else { false }
}

fn remove_duplicate_in_vec<T>(input: &mut Vec<T>)
where
    T: Hash + Eq,
{
    let FxHashSet: FxHashSet<_> = input.drain(..).into_iter().collect();
    input.extend(FxHashSet);
}

/// Assocaite type is defined with trait. So we should use self_trait as a parameter
fn replace_self_associate_types(
    raw_type: &clean::Type,
    self_trait: &Option<clean::Type>,
    associate_type_map: &FxHashMap<String, clean::Type>,
) -> clean::Type {
    if *self_trait == None {
        return raw_type.to_owned();
    }
    match raw_type.to_owned() {
        clean::Type::QPath { name, trait_: raw_self_trait, .. } => {
            let self_trait = self_trait.as_ref().unwrap().to_owned();
            if *raw_self_trait == self_trait && associate_type_map.contains_key(&name) {
                associate_type_map.get(&name).unwrap().to_owned()
            } else {
                raw_type.to_owned()
            }
        }
        clean::Type::RawPointer(mutability, inner_type) => {
            let new_type =
                replace_self_associate_types(&*inner_type, self_trait, associate_type_map);
            clean::Type::RawPointer(mutability, Box::new(new_type))
        }
        clean::Type::BorrowedRef { lifetime, mutability, type_ } => {
            let new_type = replace_self_associate_types(&*type_, self_trait, associate_type_map);
            clean::Type::BorrowedRef { lifetime, mutability, type_: Box::new(new_type) }
        }
        clean::Type::Slice(inner_type) => {
            let new_type =
                replace_self_associate_types(&*inner_type, self_trait, associate_type_map);
            clean::Type::Slice(Box::new(new_type))
        }
        clean::Type::Array(inner_type, length) => {
            let new_type =
                replace_self_associate_types(&*inner_type, self_trait, associate_type_map);
            clean::Type::Array(Box::new(new_type), length)
        }
        clean::Type::Tuple(types) => {
            let new_types = types
                .into_iter()
                .map(|type_| replace_self_associate_types(&type_, self_trait, associate_type_map))
                .collect_vec();
            clean::Type::Tuple(new_types)
        }
        clean::Type::Path { path} => {
            let clean::Path { res, segments } = path;
            let new_segments = segments
                .into_iter()
                .map(|path_segment| {
                    let clean::PathSegment { name, args } = path_segment;
                    let new_args = match args {
                        clean::GenericArgs::AngleBracketed { args, bindings } => {
                            let new_args = args
                                .into_iter()
                                .map(|generic_arg| {
                                    if let clean::GenericArg::Type(type_) = generic_arg {
                                        let new_type = replace_self_associate_types(
                                            &type_,
                                            self_trait,
                                            associate_type_map,
                                        );
                                        clean::GenericArg::Type(new_type)
                                    } else {
                                        generic_arg
                                    }
                                })
                                .collect_vec();
                            clean::GenericArgs::AngleBracketed { args: new_args, bindings }
                        }
                        clean::GenericArgs::Parenthesized { inputs, output } => {
                            let new_inputs = inputs
                                .into_iter()
                                .map(|type_| {
                                    replace_self_associate_types(
                                        &type_,
                                        self_trait,
                                        associate_type_map,
                                    )
                                })
                                .collect_vec();
                            let new_output = output.map(|type_| {
                                replace_self_associate_types(&type_, self_trait, associate_type_map)
                            });
                            clean::GenericArgs::Parenthesized {
                                inputs: new_inputs,
                                output: new_output,
                            }
                        }
                    };
                    clean::PathSegment { name, args: new_args }
                })
                .collect_vec();
            let new_path = clean::Path { res, segments: new_segments };
            clean::Type::Path { path: new_path}
        }
        _ => raw_type.to_owned(),
    }
}

/// where predicate contains restrict_generic
pub fn where_preidicates_bounds_restrict_generic(generics: &Generics) -> bool {
    generics.where_predicates.iter().any(|where_predicate| {
        if let clean::WherePredicate::BoundPredicate { ty, .. } = where_predicate {
            match ty {
                // Generic and QPath are free generic
                clean::Type::Generic(..) | clean::Type::QPath { .. } => false,
                // restrict generic
                _ => true,
            }
        } else {
            false
        }
    })
}
