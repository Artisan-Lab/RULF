use crate::clean::Path;
use crate::clean::{self, types::PrimitiveType, Type};
use crate::clean::{types, GenericArg, GenericArgs, PathSegment, TypeBinding, Lifetime};
use crate::formats::cache::Cache;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzzable_type::{self, FuzzableCallType};
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::impl_util::FullNameMap;
use rustc_span::Symbol;
use crate::fuzz_target::prelude_type::{self, PreludeType};
use crate::html::format::join_with_double_colon;
use crate::fuzz_target::api_function::ApiFunction;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_hir::{self, Mutability};
use std::cmp::max;

use super::generic_function::GenericFunction;
use super::{api_function, generic_function};

pub(crate) fn extract_input_types(inputs: &clean::Arguments) -> Vec<clean::Type> {
    inputs.values.iter().map(|arg| arg.type_.clone()).collect()
}

pub(crate) fn extract_output_type(output: &clean::FnRetTy) -> Option<clean::Type> {
    match output {
        clean::FnRetTy::Return(ty) => Some(ty.clone()),
        clean::FnRetTy::DefaultReturn => None,
    }
}

pub(crate) fn is_external_type(did: DefId, cache: &Cache) -> bool {
    if let Some(&(ref syms, item_type)) = cache.paths.get(&did) {
        return false;
    } else if let Some(&(ref syms, item_type)) = cache.external_paths.get(&did) {
        return true;
    } else {
        panic!("did could not be found in cache");
    }
}

fn get_internal_type_name_from_did(did: DefId, cache: &Cache) -> Option<String> {
    if let Some(&(ref syms, item_type)) = cache.paths.get(&did) {
        Some(join_with_double_colon(syms))
    } else {
        None
    }
}

pub(crate) fn get_type_name_from_did(did: DefId, cache: &Cache) -> Option<String> {
    if let Some(&(ref syms, item_type)) = cache.paths.get(&did) {
        Some(join_with_double_colon(syms))
    } else if let Some(&(ref syms, item_type)) = cache.external_paths.get(&did) {
        Some(join_with_double_colon(syms))
    } else {
        None
    }
}

fn map_std_type_name(name: &str) -> String {
    if name.starts_with("alloc::") { "std::".to_owned() + &name[7..] } else { name.to_string() }
}

pub(crate) fn is_generic_type(ty: &clean::Type) -> bool {
    //TODO：self不需要考虑，因为在产生api function的时候就已经完成转换，但需要考虑类型嵌套的情况
    match ty {
        clean::Type::Generic(_) => true,
        clean::Type::ImplTrait(_) => true,
        clean::Type::Primitive(_) => false,
        clean::Type::QPath(qpathdata) => is_generic_type(&qpathdata.self_type), // associate item
        clean::Type::Path { path } => {
            let segments = &path.segments;
            for segment in segments {
                let generic_args = &segment.args;
                match generic_args {
                    clean::GenericArgs::AngleBracketed { args, .. } => {
                        for generic_arg in args.iter() {
                            if let clean::GenericArg::Type(inner_ty) = generic_arg {
                                if is_generic_type(inner_ty) {
                                    return true;
                                }
                            }
                        }
                    }
                    clean::GenericArgs::Parenthesized { inputs, output } => {
                        for input_ty in inputs.iter() {
                            if is_generic_type(input_ty) {
                                return true;
                            }
                        }
                        if let Some(output_ty) = output {
                            if is_generic_type(&output_ty) {
                                return true;
                            }
                        }
                    }
                }
            }
            return false;
        }
        clean::Type::Tuple(types) => {
            for ty_ in types {
                if is_generic_type(ty_) {
                    return true;
                }
            }
            return false;
        }
        clean::Type::Slice(type_)
        | clean::Type::Array(type_, ..)
        | clean::Type::RawPointer(_, type_)
        | clean::Type::BorrowedRef { type_, .. } => {
            let inner_type = &**type_;
            return is_generic_type(inner_type);
        }
        clean::Type::DynTrait(..) => {
            return true;
        }
        _ => {
            //TODO:implTrait是否当作泛型呢？QPath是否当作泛型呢？
            //如果有不支持的类型，也可以往这个函数里面丢，会在将函数加到图里面的时候最后过滤一遍
            unimplemented!("is_generic_type: not support this type: {ty:?}");
        }
    }
}

pub(crate) fn _is_end_type(ty: &clean::Type, full_name_map: &FullNameMap, cache: &Cache) -> bool {
    match ty {
        clean::Type::Path { .. } => {
            //TODO:need more analyse
            if prelude_type::_prelude_type_need_special_dealing(ty, full_name_map, cache) {
                let prelude_type = PreludeType::from_type(ty, full_name_map, cache);
                let final_type = prelude_type._get_final_type();
                if _is_end_type(&final_type, full_name_map, cache) {
                    return true;
                }
            }
            return false;
        }
        clean::Type::Generic(_s) => {
            //println!("generic type = {:?}", s);
            false
        }
        clean::Type::Primitive(_) => true,
        clean::Type::BareFunction(_) => false,
        clean::Type::Tuple(inner) => {
            let mut flag = true;
            for inner_type in inner {
                if !_is_end_type(inner_type, full_name_map, cache) {
                    flag = false;
                    break;
                }
            }
            flag
        }
        clean::Type::Slice(inner)
        | clean::Type::Array(inner, ..)
        | clean::Type::RawPointer(_, inner) => {
            let inner_type = &**inner;
            return _is_end_type(inner_type, full_name_map, cache);
        }
        clean::Type::BorrowedRef { type_, .. } => {
            let inner_type = &**type_;
            return _is_end_type(inner_type, full_name_map, cache);
        }
        clean::Type::QPath { .. } => {
            //TODO: qpathx
            false
        }
        clean::Type::Infer => false,
        clean::Type::ImplTrait(_) => {
            //TODO: impl trait
            false
        }
        clean::Type::DynTrait(..) => false,
        _ => {
            unimplemented!();
        }
    }
}

pub(crate) fn print_path_segment(
    full_name: Option<String>,
    segment: &PathSegment,
    cache: Option<&Cache>,
) -> String {
    let mut res = String::new();
    if let Some(name) = full_name {
        res.push_str(&name);
    } else {
        res.push_str(&segment.name.as_str());
    }

    match &segment.args {
        GenericArgs::AngleBracketed { args, bindings } => {
            let mut syms = Vec::<String>::new();
            for arg in args.iter() {
                let sym = match arg {
                    GenericArg::Lifetime(lifetime) =>
                    /* lifetime.0.to_string() */
                    {
                        lifetime.0.to_string()
                    }
                    GenericArg::Const(constant) => _type_name(&constant.type_, cache),
                    GenericArg::Type(type_) => _type_name(&type_, cache),
                    GenericArg::Infer => "_".to_owned(),
                };
                syms.push(sym);
            }
            for binding in bindings.iter() {
                let assoc_item = print_path_segment(None, &binding.assoc, cache);
                let value = match binding.kind {
                    clean::TypeBindingKind::Equality { ref term } => {
                        format!("={}", print_term(term, cache))
                    }
                    clean::TypeBindingKind::Constraint { ref bounds } => format!(":{:?}", bounds),
                };
                syms.push(format!("{}{}", assoc_item, value));
            }
            let syms = syms.join(", ");
            if !syms.is_empty() {
                res.push_str(&format!("<{syms}>"));
            }
        }
        GenericArgs::Parenthesized { inputs, output } => {
            res.push_str("Fn(<unknown>) -> <unknown>");
        }
    };
    res
}

pub(crate) fn print_term(term: &types::Term, cache: Option<&Cache>) -> String {
    match term {
        clean::Term::Type(ty) => _type_name(ty, cache),
        clean::Term::Constant(constant) => "<constant>".to_string(),
    }
}

pub(crate) fn print_path(path: &Path, cache: Option<&Cache>) -> String {
    let full_name = cache.and_then(|cache| get_type_name_from_did(path.def_id(), cache)).as_ref().map(|x| map_std_type_name(x));
    let mut res = Vec::<String>::new();
    if !path.segments.is_empty() {
        res.push(print_path_segment(full_name, &path.segments[0], cache));
        for segment in path.segments.iter().skip(1) {
            res.push(print_path_segment(None, segment, cache));
        }
    }

    res.join("::").to_string()
}

//get the name of a type
pub(crate) fn _type_name(type_: &clean::Type, cache: Option<&Cache>) -> String {
    match type_ {
        clean::Type::Path { path } => print_path(path, cache),
        clean::Type::Primitive(primitive_type) => primitive_type.as_sym().to_string(),
        clean::Type::Generic(generic) => generic.to_string(),
        clean::Type::BorrowedRef { type_, mutability, lifetime } => {
            let inner_type = &**type_;
            let inner_name = _type_name(inner_type, cache);
            let mut_tag= match mutability {
                Mutability::Not => "",
                Mutability::Mut => "mut "
            };
            let life_str=match lifetime{
                Some(lifetime)=>lifetime.0.to_string()+" ",
                None => "".to_string()
            };
            format!("&{}{}{}",life_str,mut_tag,inner_name)
        }
        clean::Type::Slice(type_) => {
            format!("[{}]", _type_name(type_, cache))
        }
        clean::Type::Array(type_, str_) => {
            format!("[{};{}]", _type_name(type_, cache), str_)
        }
        clean::Type::Tuple(inner_types) => {
            let inner_types_number = inner_types.len();
            let mut res = "(".to_string();
            for i in 0..inner_types_number {
                let inner_type = &inner_types[i];
                if i != 0 {
                    res.push_str(" ,");
                }
                res.push_str(_type_name(inner_type, cache).as_str());
            }
            res.push(')');
            res
        }
        clean::Type::ImplTrait(bounds) => {
            let mut def_set = GenericParamMap::new();
            def_set.add_generic_bounds("impl", bounds);
            format!("impl {:?}", def_set)
        }
        clean::Type::QPath(qpathdata) => {
            format!(
                "<{} as {}>::{}",
                _type_name(&qpathdata.self_type, cache),
                print_path(&qpathdata.trait_, cache),
                print_path_segment(None, &qpathdata.assoc, cache),
            )
        }
        clean::Type::Infer => "_".to_string(),
        clean::Type::RawPointer(mutability, type_) => match mutability {
            Mutability::Not => format!("*const {}", _type_name(type_, cache)),
            Mutability::Mut => format!("*{}", _type_name(type_, cache)),
        },
        _ => format!("Currently not supported: {:?}", type_),
    }
}

pub(crate) fn _same_type(
    output_type: &clean::Type,
    input_type: &clean::Type,
    hard_mode: bool,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> CallType {
    if hard_mode {
        _same_type_hard_mode(output_type, input_type, full_name_map, cache)
    } else {
        //TODO:soft mode
        CallType::_NotCompatible
    }
}

//hard_mode
pub(crate) fn _same_type_hard_mode(
    output_type: &clean::Type,
    input_type: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> CallType {
    //same type, direct call
    if output_type == input_type {
        return CallType::_DirectCall;
    }

    //对输入类型解引用,后面就不在考虑输入类型需要解引用的情况
    match input_type {
        clean::Type::BorrowedRef { mutability, type_, .. } => {
            //TODO:should take lifetime into account?
            return _borrowed_ref_in_same_type(
                mutability,
                type_,
                output_type,
                full_name_map,
                cache,
            );
        }
        clean::Type::RawPointer(mutability, type_) => {
            return _raw_pointer_in_same_type(mutability, type_, output_type, full_name_map, cache);
        }
        _ => {}
    }

    //考虑输入类型是prelude type的情况，后面就不再考虑
    if prelude_type::_prelude_type_need_special_dealing(input_type, full_name_map, cache) {
        let input_prelude_type = PreludeType::from_type(input_type, full_name_map, cache);
        let final_type = input_prelude_type._get_final_type();
        let inner_call_type = _same_type_hard_mode(output_type, &final_type, full_name_map, cache);
        match inner_call_type {
            CallType::_NotCompatible => {
                return CallType::_NotCompatible;
            }
            _ => {
                return input_prelude_type._to_call_type(&inner_call_type);
            }
        }
    }

    //对输出类型进行分类讨论
    match output_type {
        //结构体、枚举、联合
        clean::Type::Path { .. } => {
            _same_type_resolved_path(output_type, input_type, full_name_map, cache)
        }
        //范型
        clean::Type::Generic(_generic) => {
            // generic match all type.
            unreachable!("should not occur generic here");
        }
        //基本类型
        //TODO:暂不考虑两次转换，如char和任意宽度的数字，但考虑char和u8的转换
        clean::Type::Primitive(primitive_type) => _same_type_primitive(primitive_type, input_type),
        clean::Type::BareFunction(_bare_function) => {
            //TODO:有需要的时候在考虑
            CallType::_NotCompatible
        }
        clean::Type::Tuple(_inner_types) => CallType::_NotCompatible,
        clean::Type::Slice(_inner_type) => CallType::_NotCompatible,
        clean::Type::Array(_inner_type, _) => CallType::_NotCompatible,
        clean::Type::Infer => CallType::_NotCompatible,
        clean::Type::RawPointer(_, type_) => {
            _same_type_raw_pointer(type_, input_type, full_name_map, cache)
        }
        clean::Type::BorrowedRef { type_, .. } => {
            _same_type_borrowed_ref(type_, input_type, full_name_map, cache)
        }
        clean::Type::QPath { .. } => {
            //TODO:有需要的时候再考虑
            CallType::_NotCompatible
        }
        clean::Type::ImplTrait(_) => {
            //TODO:有需要的时候在考虑
            CallType::_NotCompatible
        }
        clean::Type::DynTrait(..) => CallType::_NotCompatible,
    }
}

//test if types are the same type
//输出类型是Path的情况
fn _same_type_resolved_path(
    output_type: &clean::Type,
    input_type: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> CallType {
    //处理output type 是 prelude type的情况
    if prelude_type::_prelude_type_need_special_dealing(output_type, full_name_map, cache) {
        let output_prelude_type = PreludeType::from_type(output_type, full_name_map, cache);
        let final_output_type = output_prelude_type._get_final_type();
        let inner_call_type =
            _same_type_hard_mode(&final_output_type, input_type, full_name_map, cache);
        match inner_call_type {
            CallType::_NotCompatible => {
                return CallType::_NotCompatible;
            }
            _ => {
                return output_prelude_type._unwrap_call_type(&inner_call_type);
            }
        }
    }

    match input_type {
        clean::Type::Path { .. } => {
            if *output_type == *input_type {
                //if input type = outer type, then this is the same type
                //only same defid is not sufficient. eg. Option<usize> != Option<&str>
                return CallType::_DirectCall;
            } else if _resolved_path_equal_without_lifetime(output_type, input_type) {
                return CallType::_DirectCall;
            } else {
                return CallType::_NotCompatible;
            }
        }
        _ => CallType::_NotCompatible,
    }
}

//输出类型是Primitive的情况
fn _same_type_primitive(primitive_type: &PrimitiveType, input_type: &clean::Type) -> CallType {
    match primitive_type {
        PrimitiveType::Isize
        | PrimitiveType::I8
        | PrimitiveType::I16
        | PrimitiveType::I32
        | PrimitiveType::I64
        | PrimitiveType::I128
        | PrimitiveType::Usize
        | PrimitiveType::U8
        | PrimitiveType::U16
        | PrimitiveType::U32
        | PrimitiveType::U64
        | PrimitiveType::U128
        | PrimitiveType::F32
        | PrimitiveType::F64 => {
            //数字类型
            let output_primitive_type = primitive_type;
            match input_type {
                //输入类型也是基础类型
                clean::Type::Primitive(input_primitive_type) => {
                    if output_primitive_type == input_primitive_type {
                        return CallType::_DirectCall;
                    }
                    match input_primitive_type {
                        //输入类型也是数字类型，可以直接as转换
                        PrimitiveType::Isize
                        | PrimitiveType::I8
                        | PrimitiveType::I16
                        | PrimitiveType::I32
                        | PrimitiveType::I64
                        | PrimitiveType::I128
                        | PrimitiveType::Usize
                        | PrimitiveType::U8
                        | PrimitiveType::U16
                        | PrimitiveType::U32
                        | PrimitiveType::U64
                        | PrimitiveType::U128
                        | PrimitiveType::F32
                        | PrimitiveType::F64 => {
                            if output_primitive_type == input_primitive_type {
                                return CallType::_DirectCall;
                            } else {
                                return CallType::_AsConvert(
                                    input_primitive_type.as_sym().to_string(),
                                );
                            }
                        }
                        //输入类型是字符类型，当输出类型是U8的时候，可以as强转
                        PrimitiveType::Char => {
                            if *output_primitive_type == PrimitiveType::U8 {
                                return CallType::_AsConvert(
                                    input_primitive_type.as_sym().to_string(),
                                );
                            } else {
                                return CallType::_NotCompatible;
                            }
                        }
                        PrimitiveType::Bool
                        | PrimitiveType::Str
                        | PrimitiveType::Slice
                        | PrimitiveType::Array
                        | PrimitiveType::Tuple
                        | PrimitiveType::Unit
                        | PrimitiveType::RawPointer
                        | PrimitiveType::Reference
                        | PrimitiveType::Fn
                        | PrimitiveType::Never => {
                            return CallType::_NotCompatible;
                        }
                    }
                }
                _ => return CallType::_NotCompatible,
            }
        }
        PrimitiveType::Char => match input_type {
            clean::Type::Primitive(inner_primitive_type) => match inner_primitive_type {
                PrimitiveType::Char => {
                    return CallType::_DirectCall;
                }
                PrimitiveType::U8 => {
                    return CallType::_AsConvert(inner_primitive_type.as_sym().to_string());
                }
                _ => {
                    return CallType::_NotCompatible;
                }
            },
            _ => CallType::_NotCompatible,
        },
        _ => CallType::_NotCompatible,
    }
}

//输出类型是RawPointer的情况
fn _same_type_raw_pointer(
    type_: &Box<clean::Type>,
    input_type: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> CallType {
    let inner_type = &**type_;
    let inner_compatible = _same_type_hard_mode(inner_type, input_type, full_name_map, cache);
    match inner_compatible {
        CallType::_NotCompatible => {
            return CallType::_NotCompatible;
        }
        _ => {
            return CallType::_UnsafeDeref(Box::new(inner_compatible));
        }
    }
}

//输出类型是BorrowedRef的情况
fn _same_type_borrowed_ref(
    type_: &Box<clean::Type>,
    input_type: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> CallType {
    let inner_type = &**type_;
    let inner_compatible = _same_type_hard_mode(inner_type, input_type, full_name_map, cache);
    match inner_compatible {
        CallType::_NotCompatible => {
            return CallType::_NotCompatible;
        }
        _ => {
            //如果是可以copy的类型，那么直接解引用;否则的话则认为是不能兼容的
            if _copy_type(inner_type) {
                return CallType::_Deref(Box::new(inner_compatible));
            } else {
                //TODO:是否需要考虑可以clone的情况？
                return CallType::_NotCompatible;
            }
        }
    }
}

//作为下个函数的输入类型：second type
//处理输入类型是引用的情况
pub(crate) fn _borrowed_ref_in_same_type(
    mutability: &Mutability,
    type_: &Box<clean::Type>,
    output_type: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> CallType {
    let inner_type = &**type_;
    let inner_compatible = _same_type_hard_mode(output_type, inner_type, full_name_map, cache);
    match &inner_compatible {
        CallType::_NotCompatible => {
            return CallType::_NotCompatible;
        }
        _ => match mutability {
            Mutability::Mut => {
                return CallType::_MutBorrowedRef(Box::new(inner_compatible.clone()));
            }
            Mutability::Not => {
                return CallType::_BorrowedRef(Box::new(inner_compatible.clone()));
            }
        },
    }
}

//处理输入类型是裸指针的情况
pub(crate) fn _raw_pointer_in_same_type(
    mutability: &Mutability,
    type_: &Box<clean::Type>,
    output_type: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> CallType {
    let inner_type = &**type_;
    let inner_compatible = _same_type_hard_mode(output_type, inner_type, full_name_map, cache);
    match &inner_compatible {
        CallType::_NotCompatible => {
            return CallType::_NotCompatible;
        }
        _ => match mutability {
            Mutability::Mut => {
                return CallType::_MutRawPointer(
                    Box::new(inner_compatible.clone()),
                    inner_type.clone(),
                );
            }
            Mutability::Not => {
                return CallType::_ConstRawPointer(
                    Box::new(inner_compatible.clone()),
                    inner_type.clone(),
                );
            }
        },
    }
}

//判断一个类型是否是按照copy语义来进行穿参的
pub(crate) fn _copy_type(type_: &clean::Type) -> bool {
    match type_ {
        clean::Type::Path { .. } => {
            //TODO:结构体可能是可以copy的，要看有没有实现copy trait
            return false;
        }
        clean::Type::Generic(_) => {
            //TODO:范型可能是可以copy的，要看有没有copy trait的约束
            return false;
        }
        clean::Type::Primitive(primitive_type) => match primitive_type {
            PrimitiveType::Isize
            | PrimitiveType::I8
            | PrimitiveType::I16
            | PrimitiveType::I32
            | PrimitiveType::I64
            | PrimitiveType::I128
            | PrimitiveType::Usize
            | PrimitiveType::U8
            | PrimitiveType::U16
            | PrimitiveType::U32
            | PrimitiveType::U64
            | PrimitiveType::U128
            | PrimitiveType::F32
            | PrimitiveType::F64
            | PrimitiveType::Char
            | PrimitiveType::Bool => {
                return true;
            }
            _ => {
                return false;
            }
        },
        clean::Type::BareFunction(_) | clean::Type::Infer => return false,
        clean::Type::Tuple(types) => {
            //如果全都是可以copy的，那么整个元组也是可以copy的
            for ty_ in types {
                if !_copy_type(ty_) {
                    return false;
                }
            }
            return true;
        }
        clean::Type::Slice(_type) => {
            //TODO:暂时不确定
            return false;
        }
        clean::Type::Array(type_, _) => {
            let inner_type = &**type_;
            if _copy_type(inner_type) {
                return true;
            } else {
                return false;
            }
        }
        clean::Type::RawPointer(..) => {
            return true;
        }
        clean::Type::BorrowedRef { mutability, .. } => match mutability {
            Mutability::Mut => {
                return false;
            }
            Mutability::Not => {
                return true;
            }
        },
        clean::Type::QPath { .. } => {
            //TODO:不确定,遇到再看
            return false;
        }
        clean::Type::ImplTrait(_) => {
            //TODO:不确定，遇到再看
            return false;
        }
        _ => {
            unimplemented!();
        }
    }
}

//判断move会发生的条件：
//目前逻辑有些问题
//输入类型不是copy_type，并且调用方式是Direct call, Deref ，UnsafeDeref
pub(crate) fn _move_condition(input_type: &clean::Type, call_type: &CallType) -> bool {
    if call_type._contains_move_call_type() {
        return true;
    }
    if !_copy_type(input_type) {
        match call_type {
            CallType::_DirectCall
            | CallType::_Deref(..)
            | CallType::_UnsafeDeref(..)
            | CallType::_UnwrapOption(..)
            | CallType::_UnwrapResult(..) => {
                return true;
            }
            _ => {}
        }
    }
    return false;
}

pub(crate) fn is_fuzzable_type(
    ty_: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> bool {
    let fuzzable = fuzzable_type::fuzzable_call_type(ty_, full_name_map, cache);
    match fuzzable {
        FuzzableCallType::NoFuzzable => false,
        _ => true,
    }
}

pub(crate) fn _is_mutable_borrow_occurs(input_type_: &clean::Type, call_type: &CallType) -> bool {
    //TODO:暂时先这样处理，后面等调整了result处理的逻辑再进行处理
    if call_type._contains_move_call_type() {
        return false;
    }

    match input_type_ {
        clean::Type::BorrowedRef { mutability, .. } | clean::Type::RawPointer(mutability, _) => {
            if let Mutability::Mut = *mutability {
                match call_type {
                    CallType::_DirectCall
                    | CallType::_MutBorrowedRef(..)
                    | CallType::_MutRawPointer(..) => {
                        return true;
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
    return false;
}

pub(crate) fn _is_immutable_borrow_occurs(input_type: &clean::Type, call_type: &CallType) -> bool {
    match input_type {
        clean::Type::BorrowedRef { mutability, .. } | clean::Type::RawPointer(mutability, _) => {
            if let Mutability::Not = *mutability {
                match call_type {
                    CallType::_DirectCall
                    | CallType::_BorrowedRef(..)
                    | CallType::_ConstRawPointer(..) => {
                        return true;
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
    return false;
}

pub(crate) fn _need_mut_tag(call_type: &CallType) -> bool {
    match call_type {
        CallType::_MutBorrowedRef(..) | CallType::_MutRawPointer(..) => true,
        _ => false,
    }
}

pub(crate) fn _resolved_path_equal_without_lifetime(
    ltype: &clean::Type,
    rtype: &clean::Type,
) -> bool {
    if let clean::Type::Path { path: lpath, .. } = ltype {
        if let clean::Type::Path { path: rpath, .. } = rtype {
            if lpath.generics().is_some() || rpath.generics().is_some() {
                return false;
            }
            if lpath.def_id() != rpath.def_id() {
                return false;
            }
            let clean::Path { /* global: lglobal, */ res: lres, segments: lsegments } = lpath;
            let clean::Path { /* global: rglobal, */ res: rres, segments: rsegments } = rpath;
            let lsegment_len = lsegments.len();
            let rsegment_len = rsegments.len();

            if
            /* *lglobal != *rglobal || */
            *lres != *rres || lsegment_len != rsegment_len {
                return false;
            }
            let l_segments_without_lifetime = new_segments_without_lifetime(lsegments);
            let r_segments_without_lifetime = new_segments_without_lifetime(rsegments);

            for i in 0..lsegment_len {
                if l_segments_without_lifetime[i] != r_segments_without_lifetime[i] {
                    return false;
                }
            }
            return true;
        }
    }
    return false;
}

fn new_segments_without_lifetime(
    old_path_segments: &Vec<clean::PathSegment>,
) -> Vec<clean::PathSegment> {
    let mut new_segments_without_lifetime = Vec::new();
    for old_path_segment in old_path_segments {
        let segment_name = &old_path_segment.name;
        let generic_args = &old_path_segment.args;
        if let clean::GenericArgs::AngleBracketed { args, bindings } = generic_args {
            let mut new_args = Vec::new();
            for arg in args.iter() {
                match arg {
                    clean::GenericArg::Lifetime(..) => {}
                    clean::GenericArg::Const(..) | clean::GenericArg::Type(..) => {
                        new_args.push(arg.clone());
                    }
                    _ => {
                        unimplemented!();
                    }
                }
            }
            let new_generic_args = clean::GenericArgs::AngleBracketed {
                args: new_args.into(),
                bindings: bindings.clone(),
            };
            let new_path_segment =
                clean::PathSegment { name: segment_name.clone(), args: new_generic_args };
            new_segments_without_lifetime.push(new_path_segment);
        } else {
            new_segments_without_lifetime.push(old_path_segment.clone());
        }
    }
    new_segments_without_lifetime
}

pub(crate) fn replace_type_lifetime(type_: &mut Type){
    let mut replace_lifetime = |type_: &mut Type| -> bool {
        match type_ {
            Type::Path { ref mut path } => {
                for segment in path.segments.iter_mut() {
                    if let GenericArgs::AngleBracketed { ref mut args, .. } = segment.args {
                        for arg in args.iter_mut() {
                            match arg {
                                GenericArg::Lifetime(lifetime) => {
                                    *lifetime = Lifetime(Symbol::intern("'_"))
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
            Type::BorrowedRef { ref mut lifetime, type_, mutability } => {
                *lifetime=None;
            },
            _ => {}
        }
        true
    };
    replace_type_with(type_, &mut replace_lifetime);
}

pub(crate) fn replace_lifetime(api_fun: &mut ApiFunction){
    for input in api_fun.inputs.iter_mut(){
        replace_type_lifetime(input);
    }
    if let Some(ref mut output) = api_fun.output{
        replace_type_lifetime(output);
    }
}

pub(crate) fn replace_type_with<F: FnMut(&mut clean::Type) -> bool>(
    ty: &mut clean::Type,
    f: &mut F,
){
    if !f(ty){
        return;
    }
    // If we meet nested type, travel all type
    match ty {
        clean::Type::Path { ref mut path } => {
            for segment in path.segments.iter_mut() {
                match segment.args {
                    clean::GenericArgs::AngleBracketed { ref mut args, .. } => {
                        for generic_arg in args.iter_mut() {
                            if let clean::GenericArg::Type(ref mut inner_ty) = generic_arg {
                                replace_type_with(inner_ty, f);
                            }
                        }
                    }
                    clean::GenericArgs::Parenthesized { ref mut inputs, ref mut output } => {
                        for input_ty in inputs.iter_mut() {
                            replace_type_with(input_ty, f);
                        }
                        if let Some(ref mut output_ty) = output {
                            replace_type_with(output_ty, f);
                        }
                    }
                }
            }
        }
        clean::Type::Tuple(ref mut types) => {
            for ty_ in types {
                replace_type_with(ty_, f);
            }
        }
        clean::Type::Slice(ref mut type_)
        | clean::Type::Array(ref mut type_, ..)
        | clean::Type::RawPointer(_, ref mut type_)
        | clean::Type::BorrowedRef { ref mut type_, .. } => {
            replace_type_with(type_, f);
        }
        _ => {}
    }

}

pub(crate) fn is_binding_match(a: &TypeBinding, b: &TypeBinding) -> bool {
    if a.assoc.name.as_str() != b.assoc.name.as_str() || a.term() != b.term() {
        false
    } else {
        true
    }
}

// ty_a is concrete , ty_b
pub(crate) fn is_type_match(ty_a: &clean::Type, ty_b: &clean::Type) -> bool {
    match (ty_a, ty_b) {
        (clean::Type::Generic(_), _) | (_, clean::Type::Generic(_)) => {
            return true;
        }
        (clean::Type::ImplTrait(_), _) | (_, clean::Type::ImplTrait(_)) => {
            unimplemented!("is_type_match ImplTrait");
        }
        (clean::Type::Path { path: a }, clean::Type::Path { path: b }) => {
            if a.def_id() != b.def_id() {
                return false;
            }
            let a_args = &a.segments.last().unwrap().args;
            let b_args = &b.segments.last().unwrap().args;
            if matches!(a_args, GenericArgs::Parenthesized { .. })
                || matches!(a_args, GenericArgs::Parenthesized { .. })
            {
                println!("ignore unsupport parenthesized args:\n{:?}\n{:?}", a, b);
                return false;
            }
            if let (
                GenericArgs::AngleBracketed { args: a_args, bindings: a_bindings },
                GenericArgs::AngleBracketed { args: b_args, bindings: b_bindings },
            ) = (a_args, b_args)
            {
                for i in 0..a_args.len() {
                    if let (GenericArg::Type(a_arg), GenericArg::Type(b_arg)) =
                        (&a_args[i], &b_args[i])
                    {
                        if !is_type_match(&a_arg, &b_arg) {
                            return false;
                        }
                    } else {
                        println!(
                            "ignore unsupport generic Args (Const or Lifetime): {:?} {:?}",
                            a_args[i], b_args[i]
                        );
                    }
                }
            }
            return true;
        }
        (clean::Type::Tuple(a), clean::Type::Tuple(b)) => {
            if a.len() != b.len() {
                return false;
            }
            for (a, b) in a.iter().zip(b.iter()) {
                if (!is_type_match(a, b)) {
                    return false;
                }
            }
            return true;
        }
        (clean::Type::Slice(a), clean::Type::Slice(b))
        | (clean::Type::Array(a, ..), clean::Type::Array(b, ..))
        | (clean::Type::RawPointer(_, a), clean::Type::RawPointer(_, b))
        | (clean::Type::BorrowedRef { type_: a, .. }, clean::Type::BorrowedRef { type_: b, .. }) => {
            return is_type_match(a, b);
        }
        (clean::Type::DynTrait(..), clean::Type::DynTrait(..)) => {
            return false;
        }
        _ => {
            unimplemented!();
        }
    }
}

//递归判断一个参数是否是self类型的
//TODO：考虑在resolved path里面的括号里面可能存在self type
pub(crate) fn is_param_self_type(ty_: &clean::Type) -> bool {
    if ty_.is_self_type() {
        return true;
    }
    match ty_ {
        clean::Type::BorrowedRef { type_, .. } => {
            let inner_ty = &**type_;
            is_param_self_type(inner_ty)
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
pub(crate) fn replace_self_type(self_type: &clean::Type, impl_type: &clean::Type) -> clean::Type {
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
        clean::Type::Path { path } => {
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

pub(crate) fn type_depth(type_: &Type) -> usize {
    1 + match type_ {
        Type::Tuple(types) => {
            let mut depth = 0usize;
            for inner in types.iter() {
                depth = max(depth, type_depth(inner));
            }
            depth
        }
        Type::Slice(type_)
        | Type::Array(type_, ..)
        | Type::RawPointer(_, type_)
        | Type::BorrowedRef { type_, .. } => type_depth(&type_),
        clean::Type::Path { path } => {
            let clean::Path { res, segments } = path;
            let mut depth = 0usize;
            for path_segment in segments {
                let clean::PathSegment { name, args: generic_args } = path_segment;
                match generic_args {
                    clean::GenericArgs::AngleBracketed { args, bindings } => {
                        for generic_arg in args.iter() {
                            if let clean::GenericArg::Type(inner_type) = generic_arg {
                                depth = max(depth, type_depth(inner_type));
                            }
                        }
                    }
                    clean::GenericArgs::Parenthesized { inputs, output } => {
                        depth = max(1, depth);
                    }
                }
            }
            depth
        }
        _ => 0, // Primitive, Generic, ImplTrait, DynTrait, QPath, Infer
    }
}
