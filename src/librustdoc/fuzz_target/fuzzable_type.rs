use crate::clean::{self, PrimitiveType};
use crate::formats::cache::Cache;
use rustc_hir::Mutability;

use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::prelude_type::PreludeType;

//如果构造一个fuzzable的变量
#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum FuzzableCallType {
    NoFuzzable,
    Primitive(PrimitiveType),
    Tuple(Vec<Box<FuzzableCallType>>),
    Slice(Box<FuzzableCallType>),
    Array(Box<FuzzableCallType>),
    ConstRawPoiner(Box<FuzzableCallType>, clean::Type),
    MutRawPoiner(Box<FuzzableCallType>, clean::Type),
    STR,
    BorrowedRef(Box<FuzzableCallType>),
    MutBorrowedRef(Box<FuzzableCallType>),
    ToOption(Box<FuzzableCallType>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum FuzzableType {
    NoFuzzable,
    Primitive(PrimitiveType),
    RefSlice(Box<FuzzableType>),
    RefStr,
    Tuple(Vec<Box<FuzzableType>>),
}

impl FuzzableCallType {
    pub(crate) fn generate_fuzzable_type_and_call_type(&self) -> (FuzzableType, CallType) {
        //println!("fuzzable call type: {:?}", self);
        match self {
            FuzzableCallType::NoFuzzable => (FuzzableType::NoFuzzable, CallType::_NotCompatible),
            FuzzableCallType::Primitive(primitive) => {
                (FuzzableType::Primitive(primitive.clone()), CallType::_DirectCall)
            }
            FuzzableCallType::Tuple(types) => {
                let mut fuzzable_types = Vec::new();
                for type_ in types {
                    let (fuzzable_type, call_type) = type_.generate_fuzzable_type_and_call_type();
                    if let FuzzableType::NoFuzzable = fuzzable_type {
                        return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                    }
                    match call_type {
                        CallType::_DirectCall => {}
                        _ => {
                            return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                        }
                    }
                    fuzzable_types.push(Box::new(fuzzable_type));
                }
                return (FuzzableType::Tuple(fuzzable_types), CallType::_DirectCall);
            }
            FuzzableCallType::ConstRawPoiner(fuzzable_call_type_, type_) => {
                let (fuzzable_type, inner_call_type) =
                    fuzzable_call_type_.generate_fuzzable_type_and_call_type();
                if let FuzzableType::NoFuzzable = fuzzable_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                } else if let CallType::_NotCompatible = inner_call_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                }
                return (
                    fuzzable_type,
                    CallType::_ConstRawPointer(Box::new(inner_call_type), type_.clone()),
                );
            }
            FuzzableCallType::MutRawPoiner(fuzzable_call_type_, type_) => {
                let (fuzzable_type, inner_call_type) =
                    fuzzable_call_type_.generate_fuzzable_type_and_call_type();
                if let FuzzableType::NoFuzzable = fuzzable_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                } else if let CallType::_NotCompatible = inner_call_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                }
                return (
                    fuzzable_type,
                    CallType::_MutRawPointer(Box::new(inner_call_type), type_.clone()),
                );
            }
            FuzzableCallType::BorrowedRef(type_) => {
                let inner_type = &**type_;
                //序列切片
                if let FuzzableCallType::Slice(slice_inner) = inner_type {
                    let (fuzzable_type, inner_call_type) =
                        slice_inner.generate_fuzzable_type_and_call_type();
                    if let FuzzableType::NoFuzzable = fuzzable_type {
                        return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                    } else if let CallType::_NotCompatible = inner_call_type {
                        return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                    }
                    return (
                        FuzzableType::RefSlice(Box::new(fuzzable_type)),
                        CallType::_DirectCall,
                    );
                }
                //一般的引用
                let (fuzzable_type, inner_call_type) =
                    inner_type.generate_fuzzable_type_and_call_type();
                if let FuzzableType::NoFuzzable = fuzzable_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                } else if let CallType::_NotCompatible = inner_call_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                }
                return (fuzzable_type, CallType::_BorrowedRef(Box::new(inner_call_type)));
            }
            FuzzableCallType::MutBorrowedRef(type_) => {
                let inner_type = &**type_;
                let (fuzzable_type, inner_call_type) =
                    inner_type.generate_fuzzable_type_and_call_type();
                if let FuzzableType::NoFuzzable = fuzzable_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                } else if let CallType::_NotCompatible = inner_call_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                }
                return (fuzzable_type, CallType::_MutBorrowedRef(Box::new(inner_call_type)));
            }
            FuzzableCallType::STR => {
                return (FuzzableType::RefStr, CallType::_DirectCall);
            }
            FuzzableCallType::ToOption(inner_fuzzable_call_type) => {
                let (fuzzable_type, inner_call_type) =
                    inner_fuzzable_call_type.generate_fuzzable_type_and_call_type();
                if let FuzzableType::NoFuzzable = fuzzable_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                } else if let CallType::_NotCompatible = inner_call_type {
                    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
                }
                return (fuzzable_type, CallType::_ToOption(Box::new(inner_call_type)));
            }
            FuzzableCallType::Array(_) | FuzzableCallType::Slice(_) => {
                return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
            } //_ => {
              //    return (FuzzableType::NoFuzzable, CallType::_NotCompatible);
              //}
        }
    }
}

impl FuzzableType {
    pub(crate) fn _is_fixed_length(&self) -> bool {
        match self {
            FuzzableType::NoFuzzable => true,
            FuzzableType::Primitive(_) => true,
            FuzzableType::RefSlice(_) => false,
            FuzzableType::RefStr => false,
            FuzzableType::Tuple(inner_fuzzables) => {
                for inner_fuzzable in inner_fuzzables {
                    if !inner_fuzzable._is_fixed_length() {
                        return false;
                    }
                }
                return true;
            }
        }
    }

    //当前变量最短需要多少个字节？
    pub(crate) fn _min_length(&self) -> usize {
        match self {
            FuzzableType::NoFuzzable => 0,
            FuzzableType::Primitive(primitive_type) => {
                match primitive_type {
                    //TODO:Bool变量的长度是多少
                    clean::PrimitiveType::I8
                    | clean::PrimitiveType::U8
                    | clean::PrimitiveType::Bool => 1,
                    clean::PrimitiveType::I16 | clean::PrimitiveType::U16 => 2,
                    clean::PrimitiveType::I32
                    | clean::PrimitiveType::U32
                    | clean::PrimitiveType::Char
                    | clean::PrimitiveType::F32 => 4,
                    //TODO:在我的64位机器上，isize,usize的宽度为8个字节
                    clean::PrimitiveType::I64
                    | clean::PrimitiveType::U64
                    | clean::PrimitiveType::F64
                    | clean::PrimitiveType::Usize
                    | clean::PrimitiveType::Isize => 8,
                    clean::PrimitiveType::I128 | clean::PrimitiveType::U128 => 16,
                    _ => 0,
                }
            }
            FuzzableType::RefSlice(inner_fuzzable) => inner_fuzzable._min_length(),
            FuzzableType::RefStr => 1,
            FuzzableType::Tuple(inner_fuzzables) => {
                let mut total_length = 0;
                for inner_fuzzable in inner_fuzzables {
                    total_length = total_length + inner_fuzzable._min_length();
                }
                total_length
            }
        }
    }

    //计算长度固定的部分所需的长度
    pub(crate) fn _fixed_part_length(&self) -> usize {
        if self._is_fixed_length() {
            return self._min_length();
        } else {
            match self {
                FuzzableType::RefStr => 0,
                FuzzableType::RefSlice(..) => 0,
                FuzzableType::Tuple(inner_fuzzables) => {
                    let mut fixed_part = 0;
                    for inner_fuzzable in inner_fuzzables {
                        let inner_length = inner_fuzzable._fixed_part_length();
                        fixed_part = fixed_part + inner_length;
                    }
                    return fixed_part;
                }
                _ => self._min_length(),
            }
        }
    }

    //计算长度不固定的参数的个数，主要是需要迭代考虑元组的内部
    pub(crate) fn _dynamic_length_param_number(&self) -> usize {
        if self._is_fixed_length() {
            return 0;
        } else {
            match self {
                FuzzableType::RefStr => 1,
                FuzzableType::RefSlice(..) => 1,
                FuzzableType::Tuple(inner_fuzzables) => {
                    let mut inner_numbers = 0;
                    for inner_fuzzable in inner_fuzzables {
                        let inner_number = inner_fuzzable._dynamic_length_param_number();
                        inner_numbers = inner_numbers + inner_number;
                    }
                    inner_numbers
                }
                _ => 0,
            }
        }
    }

    //多个可变长的维度，例如&[&str], &[&[u8]]
    pub(crate) fn _is_multiple_dynamic_length(&self) -> bool {
        match self {
            FuzzableType::RefSlice(inner_fuzzable) => {
                if !inner_fuzzable._is_fixed_length() {
                    true
                } else {
                    false
                }
            }
            FuzzableType::Tuple(inner_fuzzables) => {
                for inner_fuzzable in inner_fuzzables {
                    if inner_fuzzable._is_multiple_dynamic_length() {
                        return true;
                    }
                }
                return false;
            }
            _ => false,
        }
    }

    pub(crate) fn _to_type_string(&self) -> String {
        match self {
            FuzzableType::NoFuzzable => "nofuzzable".to_string(),
            FuzzableType::Primitive(primitive) => primitive.as_sym().to_string(),
            FuzzableType::RefSlice(inner_) => {
                let inner_string = inner_._to_type_string();
                let mut res = "&[".to_string();
                res.push_str(inner_string.as_str());
                res.push_str("]");
                res
            }
            FuzzableType::RefStr => "&str".to_string(),
            FuzzableType::Tuple(inner_types) => {
                let mut res = "(".to_string();
                let first_type = inner_types.first();
                if let Some(first) = first_type {
                    let first_string = first._to_type_string();
                    res.push_str(first_string.as_str());
                } else {
                    res.push_str(")");
                    return res;
                }
                let types_len = inner_types.len();
                for i in 1..types_len {
                    res.push_str(" ,");
                    let type_string = inner_types[i]._to_type_string();
                    res.push_str(type_string.as_str());
                }
                res.push_str(")");
                res
            }
        }
    }
}

//判断一个类型是不是fuzzable的，以及如何调用相应的fuzzable变量
pub(crate) fn fuzzable_call_type(ty_: &clean::Type, full_name_map: &FullNameMap, cache: &Cache) -> FuzzableCallType {
    match ty_ {
        clean::Type::Path { .. } => {
            let prelude_type = PreludeType::from_type(ty_, full_name_map, cache);
            //result类型的变量不应该作为fuzzable的变量。只考虑作为别的函数的返回值
            match &prelude_type {
                PreludeType::NotPrelude(..) | PreludeType::PreludeResult { .. } => {
                    FuzzableCallType::NoFuzzable
                }
                PreludeType::PreludeOption(inner_type_) => {
                    let inner_fuzzable_call_type = fuzzable_call_type(inner_type_, full_name_map, cache);
                    match inner_fuzzable_call_type {
                        FuzzableCallType::NoFuzzable => {
                            return FuzzableCallType::NoFuzzable;
                        }
                        _ => {
                            return FuzzableCallType::ToOption(Box::new(inner_fuzzable_call_type));
                        }
                    }
                }
            }
        }
        clean::Type::Generic(s) => {
            FuzzableCallType::NoFuzzable
        }
        clean::Type::Primitive(primitive_type) => {
            FuzzableCallType::Primitive(primitive_type.clone())
        }
        clean::Type::BareFunction(..) => FuzzableCallType::NoFuzzable,
        clean::Type::Tuple(types) => {
            let mut vec = Vec::new();
            for inner_type in types {
                let inner_fuzzable = fuzzable_call_type(inner_type, full_name_map, cache);
                match inner_fuzzable {
                    FuzzableCallType::NoFuzzable => {
                        return FuzzableCallType::NoFuzzable;
                    }
                    _ => {
                        vec.push(Box::new(inner_fuzzable));
                    }
                }
            }
            return FuzzableCallType::Tuple(vec);
        }
        clean::Type::Slice(inner_type) => {
            let inner_ty_ = &**inner_type;
            let inner_fuzzable = fuzzable_call_type(inner_ty_, full_name_map, cache);
            match inner_fuzzable {
                FuzzableCallType::NoFuzzable => {
                    return FuzzableCallType::NoFuzzable;
                }
                _ => {
                    return FuzzableCallType::Slice(Box::new(inner_fuzzable));
                }
            }
        }
        clean::Type::Array(inner_type, ..) => {
            let inner_ty_ = &**inner_type;
            let inner_fuzzable = fuzzable_call_type(inner_ty_, full_name_map, cache);
            match inner_fuzzable {
                FuzzableCallType::NoFuzzable => {
                    return FuzzableCallType::NoFuzzable;
                }
                _ => {
                    return FuzzableCallType::Array(Box::new(inner_fuzzable));
                }
            }
        }
        clean::Type::RawPointer(mutability, type_) => {
            let inner_type = &**type_;
            let inner_fuzzable = fuzzable_call_type(inner_type, full_name_map, cache);
            match inner_fuzzable {
                FuzzableCallType::NoFuzzable => {
                    return FuzzableCallType::NoFuzzable;
                }
                _ => match mutability {
                    Mutability::Mut => {
                        return FuzzableCallType::MutRawPoiner(
                            Box::new(inner_fuzzable),
                            inner_type.clone(),
                        );
                    }
                    Mutability::Not => {
                        return FuzzableCallType::ConstRawPoiner(
                            Box::new(inner_fuzzable),
                            inner_type.clone(),
                        );
                    }
                },
            }
        }
        clean::Type::BorrowedRef { lifetime, mutability, type_, .. } => {
            let inner_type = &**type_;
            //特别处理&str的情况，这时候可以返回一个字符串作为fuzzable的变量
            if *inner_type == clean::Type::Primitive(PrimitiveType::Str)
                && *mutability == Mutability::Not
            {
                if let Some(lifetime_) = lifetime {
                    let lifetime_string = lifetime_.0.as_str();
                    if lifetime_string == "'static" {
                        //如果是static的话，由于无法构造出来，所以只能认为是不可fuzzable的
                        return FuzzableCallType::NoFuzzable;
                    }
                }
                return FuzzableCallType::STR;
            }
            let inner_fuzzable = fuzzable_call_type(inner_type, full_name_map, cache);
            match inner_fuzzable {
                FuzzableCallType::NoFuzzable => {
                    return FuzzableCallType::NoFuzzable;
                }
                _ => match mutability {
                    Mutability::Mut => {
                        return FuzzableCallType::MutBorrowedRef(Box::new(inner_fuzzable));
                    }
                    Mutability::Not => {
                        return FuzzableCallType::BorrowedRef(Box::new(inner_fuzzable));
                    }
                },
            }
        }
        clean::Type::QPath { .. } => {
            return FuzzableCallType::NoFuzzable;
        }
        clean::Type::ImplTrait(..)| clean::Type::DynTrait(..) => {
            return FuzzableCallType::NoFuzzable;
        }
        clean::Type::Infer => {
            return FuzzableCallType::NoFuzzable;
        }
        _ => {
            unimplemented!()
        }
    }
}
