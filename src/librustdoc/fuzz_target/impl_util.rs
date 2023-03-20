use crate::clean::{self, ItemKind};
use crate::formats::item_type::ItemType;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_function::ApiUnsafety;
use crate::fuzz_target::api_graph::ApiGraph;
use crate::fuzz_target::api_util;
use crate::fuzz_target::prelude_type;
use crate::html::format::join_with_double_colon;
use rustc_hir::def_id::DefId;
use rustc_data_structures::fx::{FxHashMap};
//use rustdoc_json_types::Type::Path;
//TODO:是否需要为impl里面的method重新设计数据结构？目前沿用了ApiFunction,或者直接对ApiFunction进行扩展
//两种函数目前相差一个defaultness
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

pub(crate) fn extract_impls_from_cache(
    full_name_map: &mut FullNameMap,
    mut api_graph: &mut ApiGraph<'_>,
) {
    let _trait_impl_maps = &api_graph.cache().implementors;
    let paths = &api_graph.cache().paths;

    let mut crate_impl_collection = CrateImplCollection::new();

    //construct the map of `did to type`
    for (did, (syms, item_type)) in paths {
        let full_name = join_with_double_colon(syms);
        full_name_map.push_mapping(*did, &full_name, *item_type);
    }

    let extertal_paths = &api_graph.cache().external_paths;
    for (did, (syms, item_type)) in extertal_paths {
        let full_name = join_with_double_colon(syms);
        if prelude_type::is_preluded_type(&full_name) {
            full_name_map.push_mapping(*did, &full_name, *item_type);
        }
    }

    api_graph.set_full_name_map(&full_name_map);

    //首先提取所有type的impl
    for (did, impls) in &api_graph.cache().impls {
        //只添加可以在full_name_map中找到对应的did的type
        if full_name_map._get_full_name(*did) != None {
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
    paths.join("::")
}

pub(crate) fn _analyse_impl(
    impl_: &clean::Impl,
    full_name_map: &FullNameMap,
    api_graph: &mut ApiGraph<'_>,
) {
    let inner_items = &impl_.items;

    //BUG FIX: TRAIT作为全限定名只能用于输入类型中带有self type的情况，这样可以推测self type，否则需要用具体的类型名

    let trait_full_name = match &impl_.trait_ {
        None => None,
        Some(trait_) => {
            //println!("{:?}", trait_);
            let trait_ty_def_id = trait_.def_id();
            let trait_full_name = full_name_map._get_full_name(trait_ty_def_id);
            if let Some(trait_name) = trait_full_name {
                Some(trait_name.clone())
            } else {
                None
            }
        }
    };

    let impl_ty_def_id = impl_.for_.def_id(api_graph.cache());
    let type_full_name = if let Some(def_id) = impl_ty_def_id {
        let type_name = full_name_map._get_full_name(def_id);
        if let Some(real_type_name) = type_name {
            Some(real_type_name.clone())
        } else {
            None
        }
    } else {
        None
    };

    for item in inner_items {
        //println!("item_name, {:?}", item.name.as_ref().unwrap());
        match &*item.kind {
            //TODO:这段代码暂时没用了，impl块里面的是method item，而不是function item,暂时留着，看里面是否会出现function item
            ItemKind::FunctionItem(_function) => {
                unimplemented!("function name in impl");
                //let function_name = String::new();
                //使用全限定名称：type::f
                //function_name.push_str(type_full_name.as_str());
                //function_name.push_str("::");
                //function_name.push_str(item.name.as_ref().unwrap().as_str());
                //println!("function name in impl:{:?}", function_name);
            }
            ItemKind::MethodItem(_method, _) => {
                let decl = _method.decl.clone();
                let clean::FnDecl { inputs, output, .. } = decl;
                let generics = _method.generics.clone();
                let mut inputs = api_util::_extract_input_types(&inputs);
                let output = api_util::_extract_output_type(&output);
                //println!("input types = {:?}", inputs);

                let mut contains_self_type = false;

                let input_len = inputs.len();
                for index in 0..input_len {
                    let ty_ = &inputs[index];
                    if is_param_self_type(ty_) {
                        contains_self_type = true;
                        let raplaced_ty = replace_self_type(ty_, &impl_.for_);
                        inputs[index] = raplaced_ty;
                    }
                }
                //println!("after replace, input = {:?}", inputs);

                let output = match output {
                    None => None,
                    Some(ty_) => {
                        if is_param_self_type(&ty_) {
                            let replaced_type = replace_self_type(&ty_, &impl_.for_);
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
                        generics,
                        inputs,
                        output,
                        _trait_full_path: None,
                        _unsafe_tag: api_unsafety,
                    },
                    Some(_) => {
                        if let Some(ref real_trait_name) = trait_full_name {
                            ApiFunction {
                                full_name: method_name,
                                generics,
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

//递归判断一个参数是否是self类型的
//TODO：考虑在resolved path里面的括号里面可能存在self type
fn is_param_self_type(ty_: &clean::Type) -> bool {
    if ty_.is_self_type() {
        return true;
    }
    match ty_ {
        clean::Type::BorrowedRef { type_, .. } => {
            let inner_ty = &**type_;
            if is_param_self_type(inner_ty) {
                return true;
            } else {
                return false;
            }
        }
        clean::Type::Path { path, .. } => {
            let segments = &path.segments;
            for path_segment in segments {
                let generic_args = &path_segment.args;
                match generic_args {
                    clean::GenericArgs::AngleBracketed { args, .. } => {
                        for generic_arg in args.iter() {
                            if let clean::GenericArg::Type(generic_ty) = generic_arg {
                                if is_param_self_type(&generic_ty) {
                                    return true;
                                }
                            }
                        }
                    }
                    clean::GenericArgs::Parenthesized { inputs, output } => {
                        for input_type in inputs.iter() {
                            if is_param_self_type(input_type) {
                                return true;
                            }
                        }
                        if let Some(output_type) = output {
                            if is_param_self_type(output_type) {
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

//将self类型替换为相应的结构体类型
fn replace_self_type(self_type: &clean::Type, impl_type: &clean::Type) -> clean::Type {
    if self_type.is_self_type() {
        return impl_type.clone();
    }
    match self_type {
        clean::Type::BorrowedRef { lifetime, mutability, type_ } => {
            let inner_type = &**type_;
            if is_param_self_type(inner_type) {
                let replaced_type = replace_self_type(inner_type, impl_type);
                return clean::Type::BorrowedRef {
                    lifetime: lifetime.clone(),
                    mutability: *mutability,
                    type_: Box::new(replaced_type),
                };
            } else {
                return self_type.clone();
            }
        }
        clean::Type::Path { path /*  param_names, did, is_generic  */ } => {
            if !is_param_self_type(self_type) {
                return self_type.clone();
            }
            let clean::Path { res, segments } = path;
            let mut new_segments = Vec::new();
            for path_segment in segments {
                let clean::PathSegment { name, args: generic_args } = path_segment;
                match generic_args {
                    clean::GenericArgs::AngleBracketed { args, bindings } => {
                        let mut new_args = Vec::new();
                        for generic_arg in args.iter() {
                            if let clean::GenericArg::Type(generic_type) = generic_arg {
                                if is_param_self_type(&generic_type) {
                                    let replaced_type = replace_self_type(&generic_type, impl_type);
                                    let new_generic_arg = clean::GenericArg::Type(replaced_type);
                                    new_args.push(new_generic_arg);
                                } else {
                                    new_args.push(generic_arg.clone());
                                }
                            } else {
                                new_args.push(generic_arg.clone());
                            }
                        }
                        let new_generic_args = clean::GenericArgs::AngleBracketed {
                            args: new_args.into(),
                            bindings: bindings.clone(),
                        };
                        let new_path_segment =
                            clean::PathSegment { name: name.clone(), args: new_generic_args };
                        new_segments.push(new_path_segment);
                    }
                    clean::GenericArgs::Parenthesized { inputs, output } => {
                        let mut new_inputs = Vec::new();
                        for input_type in inputs.iter() {
                            if is_param_self_type(input_type) {
                                let replaced_type = replace_self_type(input_type, impl_type);
                                new_inputs.push(replaced_type);
                            } else {
                                new_inputs.push(input_type.clone());
                            }
                        }
                        let new_output = output.clone().map(|output_type| {
                            if is_param_self_type(&output_type) {
                                Box::new(replace_self_type(&output_type, impl_type))
                            //replace type
                            } else {
                                output_type
                            }
                        });

                        let new_generic_args = clean::GenericArgs::Parenthesized {
                            inputs: new_inputs.into(),
                            output: new_output,
                        };
                        let new_path_segment =
                            clean::PathSegment { name: name.clone(), args: new_generic_args };
                        new_segments.push(new_path_segment);
                    }
                }
            }
            let new_path = clean::Path { res: res.clone(), segments: new_segments };
            let new_type = clean::Type::Path { path: new_path };
            return new_type;
        }
        _ => {
            return self_type.clone();
        }
    }
}
