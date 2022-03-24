use crate::clean;

use super::api_function::{ApiFunction, ApiUnsafety};
use super::type_name::{type_full_name, TypeNameLevel, TypeNameMap};
use super::type_util::str_type;
use rustc_hir::Mutability;
pub enum StdHelper {
    StdPathPath(clean::Type),
    StdFfiOsStr(clean::Type),
    String(clean::Type),
}

impl StdHelper {
    pub fn new(type_: &clean::Type, type_name_map: &TypeNameMap) -> Result<Self, ()> {
        let type_full_name = type_full_name(type_, type_name_map, TypeNameLevel::All);
        match type_full_name.as_str() {
            "std::path::Path" => Ok(StdHelper::StdPathPath(type_.to_owned())),
            "std::ffi::os_str::OsStr" => Ok(StdHelper::StdFfiOsStr(type_.to_owned())),
            "String" => Ok(StdHelper::String(type_.to_owned())),
            _ => Err(()),
        }
    }

    pub fn to_helper_function(&self) -> ApiFunction {
        match self {
            StdHelper::StdPathPath(type_) => std_path_path_helper(type_),
            StdHelper::StdFfiOsStr(type_) => std_ffi_osstr_helper(type_),
            StdHelper::String(type_) => string_helper(type_),
        }
    }
}

fn std_path_path_helper(type_: &clean::Type) -> ApiFunction {
    ApiFunction {
        full_name: "std::path::Path::new".to_string(),
        generics: clean::Generics { params: Vec::new(), where_predicates: Vec::new() },
        inputs: vec![str_type()],
        output: Some(clean::Type::BorrowedRef { lifetime: None, mutability: Mutability::Not, type_: Box::new(type_.to_owned()) }),
        _trait_full_path: None,
        _unsafe_tag: ApiUnsafety::Normal,
        return_type_notation: false,
        is_helper: true,
    }
}

fn std_ffi_osstr_helper(type_: &clean::Type) -> ApiFunction {
    ApiFunction {
        full_name: "std::ffi::OsStr::new".to_string(),
        generics: clean::Generics { params: Vec::new(), where_predicates: Vec::new() },
        inputs: vec![str_type()],
        output: Some(type_.to_owned()),
        _trait_full_path: None,
        _unsafe_tag: ApiUnsafety::Normal,
        return_type_notation: false,
        is_helper: true,
    }
}

fn string_helper(type_: &clean::Type) -> ApiFunction {
    ApiFunction {
        full_name: "String::from".to_string(),
        generics: clean::Generics { params: Vec::new(), where_predicates: Vec::new() },
        inputs: vec![str_type()],
        output: Some(type_.to_owned()),
        _trait_full_path: None,
        _unsafe_tag: ApiUnsafety::Normal,
        return_type_notation: false,
        is_helper: true,
    }
}