//To deal with some prelude type
use crate::clean::{self};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_util;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::impl_util::FullNameMap;
use lazy_static::lazy_static;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};

lazy_static! {
    static ref PRELUDED_TYPE: FxHashMap<&'static str, &'static str> = {
        let mut m = FxHashMap::default();
        m.insert("core::option::Option", "Option");
        m.insert("core::result::Result", "Result");
        m.insert("alloc::string::String", "String");
        //m.insert("alloc::boxed::Box", "Box");
        m
    };
}

static _OPTION: &'static str = "Option";
static _RESULT: &'static str = "Result";
static _STRING: &'static str = "String";

pub(crate) fn is_preluded_type(type_name: &String) -> bool {
    if PRELUDED_TYPE.contains_key(type_name.as_str()) {
        return true;
    } else {
        return false;
    }
}

pub(crate) fn get_all_preluded_type() -> FxHashSet<String> {
    let mut res = FxHashSet::default();
    for (prelude_type_, _) in PRELUDED_TYPE.iter() {
        res.insert(prelude_type_.to_string());
    }
    res
}

pub(crate) fn preluded_type(
    type_: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> bool {
    let def_id = type_.def_id(cache).unwrap();
    if let Some(type_name) = full_name_map._get_full_name(def_id) {
        if is_preluded_type(type_name) {
            return true;
        }
    }
    return false;
}

pub(crate) fn to_strip_type_name(type_name: &String) -> String {
    if PRELUDED_TYPE.contains_key(type_name.as_str()) {
        PRELUDED_TYPE.get(type_name.as_str()).unwrap().to_string()
    } else {
        type_name.clone()
    }
}

//TODO:目前只考虑引用、裸指针的情况，元组，切片，数组都暂时不考虑
//暂时只考虑Result和Option
//TODO:Box,...
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub(crate) enum PreludeType {
    NotPrelude(clean::Type),
    PreludeOption(clean::Type),
    PreludeResult { ok_type: clean::Type, err_type: clean::Type },
}

impl PreludeType {
    pub(crate) fn from_type(
        type_: &clean::Type,
        full_name_map: &FullNameMap,
        cache: &Cache,
    ) -> Self {
        match type_ {
            clean::Type::Path { path, .. } => {
                if preluded_type(type_, full_name_map, cache) {
                    let def_id = type_.def_id(cache).unwrap();
                    let type_full_name = full_name_map._get_full_name(def_id).unwrap();
                    let strip_type_name_string = to_strip_type_name(type_full_name);
                    let strip_type_name = strip_type_name_string.as_str();
                    if _OPTION == strip_type_name {
                        extract_option(path, type_)
                    } else if _RESULT == strip_type_name {
                        extract_result(path, type_)
                    } else {
                        //println!("other prelude type");
                        PreludeType::NotPrelude(type_.clone())
                    }
                } else {
                    PreludeType::NotPrelude(type_.clone())
                }
            }
            _ => PreludeType::NotPrelude(type_.clone()),
        }
    }

    pub(crate) fn _to_type_name(&self, full_name_map: &FullNameMap, cache: &Cache) -> String {
        match self {
            PreludeType::NotPrelude(type_) => api_util::_type_name(type_, full_name_map, cache),
            PreludeType::PreludeOption(type_) => {
                let inner_type_name = api_util::_type_name(type_, full_name_map, cache);
                format!("Option<{}>", inner_type_name)
            }
            PreludeType::PreludeResult { ok_type, err_type } => {
                let ok_type_name = api_util::_type_name(ok_type, full_name_map, cache);
                let err_type_name = api_util::_type_name(err_type, full_name_map, cache);
                format!("Result<{}, {}>", ok_type_name, err_type_name)
            }
        }
    }

    pub(crate) fn _is_final_type(&self) -> bool {
        match self {
            PreludeType::NotPrelude(..) => true,
            PreludeType::PreludeResult { .. } | PreludeType::PreludeOption(..) => false,
        }
    }

    pub(crate) fn _get_final_type(&self) -> clean::Type {
        //获得最终的类型
        match self {
            PreludeType::NotPrelude(type_) => type_.clone(),
            PreludeType::PreludeOption(type_) => type_.clone(),
            PreludeType::PreludeResult { ok_type, .. } => {
                //Result只取ok的那部分
                ok_type.clone()
            }
        }
    }

    //How to get final type
    pub(crate) fn _unwrap_call_type(&self, inner_call_type: &CallType) -> CallType {
        match self {
            PreludeType::NotPrelude(..) => inner_call_type.clone(),
            PreludeType::PreludeOption(_type_) => {
                CallType::_UnwrapOption(Box::new(inner_call_type.clone()))
            }
            PreludeType::PreludeResult { .. } => {
                CallType::_UnwrapResult(Box::new(inner_call_type.clone()))
            }
        }
    }

    pub(crate) fn _to_call_type(&self, inner_call_type: &CallType) -> CallType {
        match self {
            PreludeType::NotPrelude(..) => inner_call_type.clone(),
            PreludeType::PreludeOption(..) => {
                CallType::_ToOption(Box::new(inner_call_type.clone()))
            }
            PreludeType::PreludeResult { .. } => {
                CallType::_ToResult(Box::new(inner_call_type.clone()))
            }
        }
    }
}

fn extract_option(path: &clean::Path, type_: &clean::Type) -> PreludeType {
    let segments = &path.segments;
    for path_segment in segments {
        let generic_args = &path_segment.args;
        match generic_args {
            clean::GenericArgs::AngleBracketed { args, .. } => {
                if args.len() != 1 {
                    continue;
                }
                let arg = &args[0];
                if let clean::GenericArg::Type(type_) = arg {
                    return PreludeType::PreludeOption(type_.clone());
                }
            }
            clean::GenericArgs::Parenthesized { .. } => {}
        }
    }
    return PreludeType::NotPrelude(type_.clone());
}

fn extract_result(path: &clean::Path, type_: &clean::Type) -> PreludeType {
    let segments = &path.segments;
    for path_segment in segments {
        let generic_args = &path_segment.args;
        match generic_args {
            clean::GenericArgs::AngleBracketed { args, .. } => {
                if args.len() != 2 {
                    continue;
                }
                let ok_arg = &args[0];
                let err_arg = &args[1];
                if let clean::GenericArg::Type(ok_type_) = ok_arg {
                    if let clean::GenericArg::Type(err_type_) = err_arg {
                        return PreludeType::PreludeResult {
                            ok_type: ok_type_.clone(),
                            err_type: err_type_.clone(),
                        };
                    }
                }
            }
            clean::GenericArgs::Parenthesized { .. } => {}
        }
    }
    return PreludeType::NotPrelude(type_.clone());
}

pub(crate) fn _prelude_type_need_special_dealing(
    type_: &clean::Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
) -> bool {
    let prelude_type = PreludeType::from_type(type_, full_name_map, cache);
    let final_type = prelude_type._get_final_type();
    if final_type == *type_ {
        false
    } else {
        true
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum _PreludeHelper {
    _ResultHelper,
    _OptionHelper,
}

impl _PreludeHelper {
    pub(crate) fn _from_call_type(call_type: &CallType) -> FxHashSet<_PreludeHelper> {
        match call_type {
            CallType::_DirectCall | CallType::_NotCompatible | CallType::_AsConvert(_) => {
                FxHashSet::default()
            }
            CallType::_BorrowedRef(inner_call_type)
            | CallType::_ConstRawPointer(inner_call_type, _)
            | CallType::_MutBorrowedRef(inner_call_type)
            | CallType::_MutRawPointer(inner_call_type, _)
            | CallType::_Deref(inner_call_type)
            | CallType::_ToOption(inner_call_type)
            | CallType::_ToResult(inner_call_type)
            | CallType::_UnsafeDeref(inner_call_type) => {
                _PreludeHelper::_from_call_type(&**inner_call_type)
            }
            CallType::_UnwrapOption(inner_call_type) => {
                let mut inner_helpers = _PreludeHelper::_from_call_type(inner_call_type);
                inner_helpers.insert(_PreludeHelper::_OptionHelper);
                inner_helpers
            }
            CallType::_UnwrapResult(inner_call_type) => {
                let mut inner_helpers = _PreludeHelper::_from_call_type(inner_call_type);
                inner_helpers.insert(_PreludeHelper::_ResultHelper);
                inner_helpers
            }
        }
    }

    pub(crate) fn _to_helper_function(&self) -> &'static str {
        match self {
            _PreludeHelper::_ResultHelper => _unwrap_result_function(),
            _PreludeHelper::_OptionHelper => _unwrap_option_function(),
        }
    }
}

fn _unwrap_result_function() -> &'static str {
    "fn _unwrap_result<T, E>(_res: Result<T, E>) -> T {
    match _res {
        Ok(_t) => _t,
        Err(_) => {
            use std::process;
            process::exit(0);
        },
    }
}\n"
}

fn _unwrap_option_function() -> &'static str {
    "fn _unwrap_option<T>(_opt: Option<T>) -> T {
    match _opt {
        Some(_t) => _t,
        None => {
            use std::process;
            process::exit(0);
        }
    }
}\n"
}
