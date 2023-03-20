use crate::clean::{self, types::PrimitiveType};
use crate::formats::cache::Cache;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzzable_type::{self, FuzzableCallType};
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::prelude_type::{self, PreludeType};
use rustc_hir::{self, Mutability};

pub(crate) fn _extract_input_types(inputs: &clean::Arguments) -> Vec<clean::Type> {
    /* let mut input_types = Vec::new();
    for argument in &inputs.values {
        let arg_ty = argument.type_.clone();
        input_types.push(arg_ty);
    }
    input_types */
    inputs.values.iter().map(|arg|{arg.type_.clone()}).collect()
}

pub(crate) fn _extract_output_type(output: &clean::FnRetTy) -> Option<clean::Type> {
    match output {
        clean::FnRetTy::Return(ty) => Some(ty.clone()),
        clean::FnRetTy::DefaultReturn => None,
    }
}

pub(crate) fn _is_generic_type(ty: &clean::Type) -> bool {
    //TODO：self不需要考虑，因为在产生api function的时候就已经完成转换，但需要考虑类型嵌套的情况
    match ty {
        clean::Type::Generic(_) => true,
        clean::Type::Path{path} => {
            if path.generics().is_some() {
                return true;
            }
            let segments = &path.segments;
            for segment in segments {
                let generic_args = &segment.args;
                match generic_args {
                    clean::GenericArgs::AngleBracketed { args, .. } => {
                        for generic_arg in args.iter() {
                            if let clean::GenericArg::Type(inner_ty) = generic_arg {
                                if _is_generic_type(inner_ty) {
                                    return true;
                                }
                            }
                        }
                    }
                    clean::GenericArgs::Parenthesized { inputs, output } => {
                        for input_ty in inputs.iter() {
                            if _is_generic_type(input_ty) {
                                return true;
                            }
                        }
                        if let Some(output_ty) = output {
                            if _is_generic_type(&output_ty) {
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
                if _is_generic_type(ty_) {
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
            return _is_generic_type(inner_type);
        }
        _ => {
            //TODO:implTrait是否当作泛型呢？QPath是否当作泛型呢？
            //如果有不支持的类型，也可以往这个函数里面丢，会在将函数加到图里面的时候最后过滤一遍
            return false;
        }
    }
}

pub(crate) fn _is_end_type(ty: &clean::Type, full_name_map: &FullNameMap, cache:&Cache) -> bool {
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
        _ => {
            unimplemented!();
        }
    }
}

//get the name of a type
pub(crate) fn _type_name(type_: &clean::Type, full_name_map: &FullNameMap, cache:&Cache) -> String {
    if let Some(def_id) = type_.def_id(cache) {
        if let Some(full_name) = full_name_map._get_full_name(def_id) {
            return full_name.clone();
        }
    }
    match type_ {
        clean::Type::Primitive(primitive_type) => primitive_type.as_sym().to_string(),
        clean::Type::Generic(generic) => generic.to_string(),
        clean::Type::BorrowedRef { type_, .. } => {
            let inner_type = &**type_;
            let inner_name = _type_name(inner_type, full_name_map, cache);
            format!("&{}", inner_name)
        }
        clean::Type::Tuple(inner_types) => {
            let inner_types_number = inner_types.len();
            let mut res = "(".to_string();
            for i in 0..inner_types_number {
                let inner_type = &inner_types[i];
                if i != 0 {
                    res.push_str(" ,");
                }
                res.push_str(_type_name(inner_type, full_name_map, cache).as_str());
            }
            res.push(')');
            res
        }
        _ => "Currently not supported".to_string(),
    }
}

pub(crate) fn _same_type(
    output_type: &clean::Type,
    input_type: &clean::Type,
    hard_mode: bool,
    full_name_map: &FullNameMap,
    cache: &Cache
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
    cache: &Cache
) -> CallType {
    //same type, direct call
    if output_type == input_type {
        return CallType::_DirectCall;
    }
    //对输入类型解引用,后面就不在考虑输入类型需要解引用的情况
    match input_type {
        clean::Type::BorrowedRef { mutability, type_, .. } => {
            //TODO:should take lifetime into account?
            return _borrowed_ref_in_same_type(mutability, type_, output_type, full_name_map, cache);
        }
        clean::Type::RawPointer(mutability, type_) => {
            return _raw_pointer_in_same_type(mutability, type_, output_type, full_name_map, cache);
        }
        _ => {}
    }

    //考虑输入类型是prelude type的情况，后面就不再考虑
    if prelude_type::_prelude_type_need_special_dealing(input_type, full_name_map, cache) {
        let input_prelude_type = PreludeType::from_type(input_type, full_name_map,cache);
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
            //TODO:范型处理，暂不考虑
            CallType::_NotCompatible
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
        _ => {
            unimplemented!();
        }
    }
}

//test if types are the same type
//输出类型是Path的情况
fn _same_type_resolved_path(
    output_type: &clean::Type,
    input_type: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache
) -> CallType {
    //处理output type 是 prelude type的情况
    if prelude_type::_prelude_type_need_special_dealing(output_type, full_name_map, cache) {
        let output_prelude_type = PreludeType::from_type(output_type, full_name_map, cache);
        let final_output_type = output_prelude_type._get_final_type();
        let inner_call_type = _same_type_hard_mode(&final_output_type, input_type, full_name_map,cache);
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
    cache: &Cache
) -> CallType {
    let inner_type = &**type_;
    let inner_compatible = _same_type_hard_mode(inner_type, input_type, full_name_map, cache);
    match inner_compatible {
        CallType::_NotCompatible => {
            return CallType::_NotCompatible;
        }, 
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
    cache: &Cache
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
    cache: &Cache
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
    cache: &Cache
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
        clean::Type::BareFunction(_)  | clean::Type::Infer => return false,
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
        _=>{
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

pub(crate) fn is_fuzzable_type(ty_: &clean::Type, full_name_map: &FullNameMap, cache: &Cache) -> bool {
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

pub(crate) fn _resolved_path_equal_without_lifetime(ltype: &clean::Type, rtype: &clean::Type) -> bool {
    if let clean::Type::Path { path: lpath, ..} = ltype
    {
        if let clean::Type::Path { path: rpath, .. } = rtype
        {
            if lpath.generics().is_some() || rpath.generics().is_some(){
                return false;
            }
            if lpath.def_id() != rpath.def_id() {
                return false;
            }
            let clean::Path { /* global: lglobal, */ res: lres, segments: lsegments } = lpath;
            let clean::Path { /* global: rglobal, */ res: rres, segments: rsegments } = rpath;
            let lsegment_len = lsegments.len();
            let rsegment_len = rsegments.len();

            if /* *lglobal != *rglobal || */ *lres != *rres || lsegment_len != rsegment_len {
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
                    },
                    _ => {unimplemented!();}
                }
            }
            let new_generic_args =
                clean::GenericArgs::AngleBracketed { args: new_args.into(), bindings: bindings.clone() };
            let new_path_segment =
                clean::PathSegment { name: segment_name.clone(), args: new_generic_args };
            new_segments_without_lifetime.push(new_path_segment);
        } else {
            new_segments_without_lifetime.push(old_path_segment.clone());
        }
    }
    new_segments_without_lifetime
}
