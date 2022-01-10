use crate::clean::{Generics, WherePredicate};
use crate::clean::{self, types::GetDefId};
use crate::fuzz_target::api_function::{ApiFunction, ApiUnsafety};
use crate::fuzz_target::api_util;
use crate::html::item_type::ItemType;
use crate::html::render::cache::Cache;
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
//TODO:是否需要为impl里面的method重新设计数据结构？目前沿用了ApiFunction,或者直接对ApiFunction进行扩展
//两种函数目前相差一个defaultness
use crate::fuzz_target::api_graph::ApiGraph;
use crate::fuzz_target::prelude_type;

#[derive(Debug, Clone)]
pub struct CrateImplCollection {
    //impl type类型的impl块
    pub impl_types: Vec<clean::Impl>,
    //impl type for trait类型的impl块
    pub impl_trait_for_types: Vec<clean::Impl>,
    //TODO:带泛型参数的impl块，但self是否该视为泛型？
    pub _generic_impl: Vec<clean::Impl>,
    pub _generic_impl_for_traits: Vec<clean::Impl>,
}

impl CrateImplCollection {
    pub fn new() -> Self {
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

    pub fn add_impl(&mut self, impl_: &clean::Impl) {
        //println!("impl type = {:?}", impl_.for_);
        let _impl_type = &impl_.for_;
        //println!("impl type = {:?}", _impl_type);
        match impl_.trait_ {
            None => {
                //println!("No trait!");
                self.impl_types.push(impl_.clone());
            }
            Some(ref _ty_) => {
                //println!("trait={:?}", _ty_);
                self.impl_trait_for_types.push(impl_.clone());
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct FullNameMap {
    pub map: HashMap<DefId, (String, ItemType)>,
}

impl FullNameMap {
    pub fn new() -> Self {
        let map = HashMap::default();
        FullNameMap { map }
    }

    pub fn push_mapping(&mut self, def_id: &DefId, full_name: &String, item_type: ItemType) {
        self.map.insert(def_id.clone(), (full_name.clone(), item_type));
    }

    pub fn _get_full_name(&self, def_id: &DefId) -> Option<&String> {
        match self.map.get(def_id) {
            None => None,
            Some((full_name, _)) => Some(full_name),
        }
    }
}

pub fn extract_impls_from_cache(
    cache: &Cache,
    full_name_map: &mut FullNameMap,
    mut api_graph: &mut ApiGraph,
) {
    let type_impl_maps = &cache.impls;
    let _trait_impl_maps = &cache.implementors;
    let paths = &cache.paths;

    let mut crate_impl_collection = CrateImplCollection::new();

    //construct the map of `did to type`
    for (did, (strings, item_type)) in paths {
        let full_name = full_path(&strings);
        full_name_map.push_mapping(&did, &full_name, *item_type);
    }

    let extertal_paths = &cache.external_paths;
    for (did, (strings, item_type)) in extertal_paths {
        let full_name = full_path(&strings);

        if prelude_type::is_preluded_type(&full_name) {
            full_name_map.push_mapping(&did, &full_name, *item_type);
        }
    }

    api_graph.set_full_name_map(&full_name_map);

    //首先提取所有type的impl
    for (did, impls) in type_impl_maps {
        //只添加可以在full_name_map中找到对应的did的type
        if full_name_map._get_full_name(did) != None {
            for impl_ in impls {
                //println!("full_name = {:?}", full_name_map._get_full_name(did).unwrap());
                crate_impl_collection.add_impl(impl_.inner_impl());
            }
        }
    }
    //println!("analyse impl Type");
    //分析impl type类型
    for impl_ in &crate_impl_collection.impl_types {
        //println!("analyse_impl_");
        _analyse_impl(impl_, &full_name_map, &mut api_graph);
    }

    //println!("analyse impl Trait for Type");
    for impl_ in &crate_impl_collection.impl_trait_for_types {
        _analyse_impl(impl_, &full_name_map, &mut api_graph);
    }
    //TODO：如何提取trait对应的impl，impl traitA for traitB? impl dyn traitA?下面的逻辑有误
    //for (did, impls) in trait_impl_maps {
    //   println!("trait:{:?}",did);
    //    //还是只看当前crate中的trait
    //    if full_name_map._get_full_name(did) != None {
    //        let full_name = full_name_map._get_full_name(did).unwrap();
    //        println!("full_name : {:?}", full_name);
    //        println!("{}", impls.len());
    //    }

    //}

    //println!("{:?}", crate_impl_collection);
}

fn full_path(paths: &Vec<String>) -> String {
    let mut full = String::new();
    match paths.first() {
        None => {
            return full;
        }
        Some(path) => {
            full.push_str(path.as_str());
        }
    }
    let paths_num = paths.len();
    for i in 1..paths_num {
        let current_path = paths[i].as_str();
        full.push_str("::");
        full.push_str(current_path);
    }

    return full;
}

pub fn _analyse_impl(impl_: &clean::Impl, full_name_map: &FullNameMap, api_graph: &mut ApiGraph) {
    let inner_items = &impl_.items;
    let impl_generics = &impl_.generics;

    //BUG FIX: TRAIT作为全限定名只能用于输入类型中带有self type的情况，这样可以推测self type，否则需要用具体的类型名
    let trait_full_name = impl_.trait_.as_ref().map(|trait_| {
        let trait_ty_def_id = &trait_.def_id().unwrap();
        let trait_full_name = full_name_map._get_full_name(trait_ty_def_id);
        trait_full_name.map(|trait_full_name| trait_full_name.to_owned())
    }).flatten();

    let impl_ty_def_id = &impl_.for_.def_id();

    let type_full_name = impl_ty_def_id.map(|ref def_id| {
        let type_name = full_name_map._get_full_name(def_id);
        type_name.map(|real_type_name| real_type_name.to_owned())
    }).flatten();

    // collect associate typedefs
    let mut associate_typedefs = HashMap::new();
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
        //println!("item_name, {:?}", item.name.as_ref().unwrap());
        match &item.inner {
            //这段代码暂时没用了，impl块里面的是method item，而不是function item,暂时留着，看里面是否会出现function item
            clean::FunctionItem(_function) => {
                let function_name = format!("{:?}::{:?}", type_full_name, item.name.as_ref().unwrap());
                //使用全限定名称：type::f
                //function_name.push_str(type_full_name.as_str());
                //function_name.push_str("::");
                //function_name.push_str(item.name.as_ref().unwrap().as_str());
                println!("function name in impl:{:?}", function_name);
            }
            clean::MethodItem(method) => {
                let clean::FnDecl { inputs, output, .. } = method.decl.clone();
                let mut method_generics = method.generics.clone();
                let mut inputs = api_util::_extract_input_types(&inputs);
                let output = api_util::_extract_output_type(&output);

                let input_contains_self_type = inputs.iter().any(|ty_| clean_type_contains_self_type(ty_));
                let output_contains_self_type = inputs.iter().any(|ty_| clean_type_contains_self_type(ty_));
                let contains_self_type = input_contains_self_type | output_contains_self_type;

                inputs = inputs.into_iter().map(|ty_| {
                    if clean_type_contains_self_type(&ty_) {
                        replace_self_type(&ty_, &impl_.for_)
                    } else {
                        ty_
                    }
                }).collect();

                let mut output = output.map(|ty_| {
                    if clean_type_contains_self_type(&ty_) {
                        replace_self_type(&ty_, &impl_.for_)
                    } else {
                        ty_
                    }
                });

                // replace associate types
                inputs = inputs.into_iter().map(|input_type| replace_self_associate_types(&input_type, &impl_.trait_, &associate_typedefs)).collect_vec();
                output = output.map(|output_type| replace_self_associate_types(&output_type, &impl_.trait_, &associate_typedefs));

                // extend method generics
                let mut generics_used_in_method = HashSet::new();
                inputs.iter().for_each(|input_type| {
                    generics_used_in_method.extend(get_generics_of_clean_type(input_type));
                });
                output.iter().for_each(|output_type| {
                    generics_used_in_method.extend(get_generics_of_clean_type(output_type));
                });

                method_generics = extend_generics(&method_generics, &impl_generics, generics_used_in_method);

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

                let api_unsafety = ApiUnsafety::_get_unsafety_from_fnheader(&method.header);
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
                            }
                        } else {
                            //println!("Trait not found in current crate.");
                            return;
                        }
                    }
                };
                api_graph.add_api_function(api_function);
            }
            _ => {
                //println!("no covered item {:?}", &item.inner);
            }
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
        clean::Type::ResolvedPath { path, .. } => {
            let segments = &path.segments;
            for path_segment in segments {
                let generic_args = &path_segment.args;
                match generic_args {
                    clean::GenericArgs::AngleBracketed { args, .. } => {
                        for generic_arg in args {
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
    let mut replace_type_map = HashMap::new();
    replace_type_map.insert(self_generic, impl_type.to_owned());
    replace_types(self_type, &replace_type_map)
}

// Add generic param appears in `ty_` to generics. These generic should also appears in `other_generics`
fn extend_generics(generics: &Generics, other_generics: &Generics, generics_used_in_method: HashSet<String>) -> Generics{
    let mut generics = generics.to_owned();
    let Generics { params: other_params , where_predicates: other_where_predicates } = other_generics;
    // let generic_param_defs_in_type = HashSet::new();
    // let where_predicates_in_type = HashSet::new();
    generics_used_in_method.into_iter().for_each(|generic_in_type| {
        let param_def = other_params.iter().filter(|generic_param_def| 
            generic_param_def.name == generic_in_type
        ).map(|generic_param_def| generic_param_def.to_owned()).collect_vec();
        // generic_param_defs_in_type.extend(param_def);
        generics.params.extend(param_def);
        let predicate = other_where_predicates.iter().filter(|where_predicate| {
            match where_predicate {
                WherePredicate::BoundPredicate{ty: where_ty,..} | WherePredicate::EqPredicate{lhs: where_ty,..} => {
                    type_is_given_generic(where_ty, &generic_in_type)
                },
                WherePredicate::RegionPredicate {..} => {
                    // We current ignore lifetime bound
                    false
                }
            }
        }).map(|where_predicate| where_predicate.to_owned()).collect_vec();
        // where_predicates.extend(predicate);
        generics.where_predicates.extend(predicate);
    });

    // remove duplicate. Not sure whether these is essential
    remove_duplicate_in_vec(&mut generics.params);
    // remove_duplicate_in_vec(&mut generics.where_predicates);

    generics
}

fn get_generics_of_clean_type(ty_: &clean::Type) -> HashSet<String> {
    let mut res = HashSet::new();
    match ty_ {
        clean::Type::Generic(generic_name) => {
            res.insert(generic_name.to_owned());
            return res;
        },
        clean::Type::ResolvedPath { .. } => {
            ty_.generics().iter().for_each(|types| {
                types.iter().for_each(|type_| {
                    let generics = get_generics_of_clean_type(type_);
                    res.extend(generics);
                });
            });
            return res;
        },
        clean::Type::BorrowedRef {type_,..} | clean::Type::Slice(type_) 
        | clean::Type::Array(type_,.. ) | clean::Type::RawPointer(_, type_) => {
            let generics = get_generics_of_clean_type(&**type_);
            res.extend(generics);
            return res;
        },
        clean::Type::Tuple(types) => {
            types.iter().for_each(|type_| {
                let generics = get_generics_of_clean_type(type_);
                res.extend(generics);
            });
            return res;
        },
        _ => res,
    }
}

/// determine clean type equals to given generic
fn type_is_given_generic(ty_: &clean::Type, given_generic: &str) -> bool {
    if let clean::Type::Generic(generic) = ty_ {
        generic == given_generic
    } else {
        false
    }
}

fn remove_duplicate_in_vec<T>(input: &mut Vec<T>) where T: Hash + Eq{
    let hashset: HashSet<_> = input.drain(..).into_iter().collect();
    input.extend(hashset);
}

/// Assocaite type is defined with trait. So we should use self_trait as a parameter
fn replace_self_associate_types(raw_type: &clean::Type, self_trait: &Option<clean::Type>, associate_type_map: &HashMap<String, clean::Type>) -> clean::Type {
    if *self_trait == None {
        return raw_type.to_owned();
    }
    match raw_type.to_owned() {
        clean::Type::QPath {name, trait_: raw_self_trait,..} => {
            let self_trait = self_trait.as_ref().unwrap().to_owned();
            if *raw_self_trait == self_trait && associate_type_map.contains_key(&name){
                associate_type_map.get(&name).unwrap().to_owned()
            } else {
                raw_type.to_owned()
            }
        }, 
        clean::Type::RawPointer(mutability, inner_type) => {
            let new_type = replace_self_associate_types(&*inner_type, self_trait, associate_type_map);
            clean::Type::RawPointer(mutability, Box::new(new_type))
        },
        clean::Type::BorrowedRef { lifetime, mutability, type_ } => {
            let new_type = replace_self_associate_types(&*type_, self_trait, associate_type_map);
            clean::Type::BorrowedRef{lifetime, mutability, type_:Box::new(new_type)}
        },
        clean::Type::Slice(inner_type) => {
            let new_type = replace_self_associate_types(&*inner_type, self_trait, associate_type_map);
            clean::Type::Slice(Box::new(new_type))
        }, 
        clean::Type::Array(inner_type, length) => {
            let new_type = replace_self_associate_types(&*inner_type, self_trait, associate_type_map);
            clean::Type::Array(Box::new(new_type), length)
        },
        clean::Type::Tuple(types) => {
            let new_types = types.into_iter().map(|type_| {
                replace_self_associate_types(&type_, self_trait, associate_type_map)
            }).collect_vec();
            clean::Type::Tuple(new_types)
        },
        clean::Type::ResolvedPath { path, param_names, did, is_generic } => {
            let clean::Path{global, res, segments} = path;
            let new_segments = segments.into_iter().map(|path_segment| {
                let clean::PathSegment{name, args} = path_segment;
                let new_args = match args {
                    clean::GenericArgs::AngleBracketed {args, bindings} => {
                        let new_args = args.into_iter().map(|generic_arg| {
                            if let clean::GenericArg::Type(type_) = generic_arg {
                                let new_type = replace_self_associate_types(&type_, self_trait, associate_type_map);
                                clean::GenericArg::Type(new_type)
                            } else {
                                generic_arg
                            }
                        }).collect_vec();
                        clean::GenericArgs::AngleBracketed {args: new_args, bindings}
                    },
                    clean::GenericArgs::Parenthesized{inputs, output} => {
                        let new_inputs = inputs.into_iter().map(|type_| {
                            replace_self_associate_types(&type_, self_trait, associate_type_map)
                        }).collect_vec();
                        let new_output = output.map(|type_| {
                            replace_self_associate_types(&type_, self_trait, associate_type_map)
                        });
                        clean::GenericArgs::Parenthesized{inputs: new_inputs, output: new_output}
                    }
                };
                clean::PathSegment{name, args: new_args}
            }).collect_vec();
            let new_path = clean::Path{global, res, segments: new_segments};
            clean::Type::ResolvedPath{path: new_path, param_names, did, is_generic}
        },
        _ => raw_type.to_owned(),
    }
}

/// replace types in raw_type with replace_type_map
fn replace_types(raw_type: &clean::Type, replace_type_map: &HashMap<clean::Type, clean::Type>) -> clean::Type {
    if replace_type_map.contains_key(raw_type) {
        return replace_type_map.get(raw_type).unwrap().to_owned();
    }

    match raw_type.to_owned() {
        clean::Type::RawPointer(mutability, inner_type) => {
            let new_type = replace_types(&*inner_type, replace_type_map);
            clean::Type::RawPointer(mutability, Box::new(new_type))
        },
        clean::Type::BorrowedRef { lifetime, mutability, type_ } => {
            let new_type = replace_types(&*type_, replace_type_map);
            clean::Type::BorrowedRef{lifetime, mutability, type_:Box::new(new_type)}
        },
        clean::Type::Slice(inner_type) => {
            let new_type = replace_types(&*inner_type, replace_type_map);
            clean::Type::Slice(Box::new(new_type))
        }, 
        clean::Type::Array(inner_type, length) => {
            let new_type = replace_types(&*inner_type, replace_type_map);
            clean::Type::Array(Box::new(new_type), length)
        },
        clean::Type::Tuple(types) => {
            let new_types = types.into_iter().map(|type_| {
                replace_types(&type_, replace_type_map)
            }).collect_vec();
            clean::Type::Tuple(new_types)
        },
        clean::Type::ResolvedPath { path, param_names, did, is_generic } => {
            let clean::Path{global, res, segments} = path;
            let new_segments = segments.into_iter().map(|path_segment| {
                let clean::PathSegment{name, args} = path_segment;
                let new_args = match args {
                    clean::GenericArgs::AngleBracketed {args, bindings} => {
                        let new_args = args.into_iter().map(|generic_arg| {
                            if let clean::GenericArg::Type(type_) = generic_arg {
                                let new_type = replace_types(&type_, replace_type_map);
                                clean::GenericArg::Type(new_type)
                            } else {
                                generic_arg
                            }
                        }).collect_vec();
                        clean::GenericArgs::AngleBracketed {args: new_args, bindings}
                    },
                    clean::GenericArgs::Parenthesized{inputs, output} => {
                        let new_inputs = inputs.into_iter().map(|type_| {
                            replace_types(&type_, replace_type_map)
                        }).collect_vec();
                        let new_output = output.map(|type_| {
                            replace_types(&type_, replace_type_map)
                        });
                        clean::GenericArgs::Parenthesized{inputs: new_inputs, output: new_output}
                    }
                };
                clean::PathSegment{name, args: new_args}
            }).collect_vec();
            let new_path = clean::Path{global, res, segments: new_segments};
            clean::Type::ResolvedPath{path: new_path, param_names, did, is_generic}
        }
        _ => raw_type.to_owned(),
    }
}