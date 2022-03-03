use std::collections::HashSet;

use crate::fuzz_target::api_util;
use crate::fuzz_target::impl_util::FullNameMap;
use itertools::Itertools;
use rustc_hir::{self, Mutability};

use crate::clean;

use super::type_name::{TypeNameMap, type_full_name, TypeNameLevel};

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum ApiUnsafety {
    Unsafe,
    Normal,
}

#[derive(Clone, Debug)]
pub struct ApiFunction {
    pub full_name: String, //函数名，要来比较是否相等
    pub generics: clean::Generics,
    pub inputs: Vec<clean::Type>,
    pub output: Option<clean::Type>,
    pub _trait_full_path: Option<String>, //Trait的全限定路径,因为使用trait::fun来调用函数的时候，需要将trait的全路径引入
    pub _unsafe_tag: ApiUnsafety,
    // 是否需要返回类型的标注
    pub return_type_notation: bool,
}

impl ApiUnsafety {
    pub fn _get_unsafety_from_fnheader(fn_header: &rustc_hir::FnHeader) -> Self {
        let unsafety = fn_header.unsafety;
        match unsafety {
            rustc_hir::Unsafety::Unsafe => ApiUnsafety::Unsafe,
            rustc_hir::Unsafety::Normal => ApiUnsafety::Normal,
        }
    }

    pub fn _is_unsafe(&self) -> bool {
        match self {
            ApiUnsafety::Unsafe => true,
            ApiUnsafety::Normal => false,
        }
    }
}

impl ApiFunction {
    pub fn _is_end_function(&self, full_name_map: &FullNameMap) -> bool {
        if self.contains_mut_borrow() {
            return false;
        }
        let return_type = &self.output;
        match return_type {
            Some(ty) => {
                api_util::_is_end_type(ty, full_name_map)
            }
            None => true,
        }
        //TODO:考虑可变引用或者是可变裸指针做参数的情况
    }

    pub fn contains_mut_borrow(&self) -> bool {
        let input_len = self.inputs.len();
        if input_len <= 0 {
            return false;
        }
        for input_type in &self.inputs {
            match input_type {
                clean::Type::BorrowedRef { mutability, .. }
                | clean::Type::RawPointer(mutability, _) => {
                    if let Mutability::Mut = mutability {
                        return true;
                    }
                }
                _ => {}
            }
        }
        return false;
    }

    pub fn contains_prelude_type_prefix(&self, prefixes: &HashSet<String>) -> bool {
        let function_name_contains_prelude_type =
            prefixes.iter().any(|prelude_type| self.full_name.starts_with(prelude_type));
        let trait_contains_prelude_type = if let Some(ref trait_name) = self._trait_full_path {
            prefixes.iter().any(|prelude_type| trait_name.starts_with(prelude_type))
        } else {
            false
        };
        !function_name_contains_prelude_type & !trait_contains_prelude_type
    }

    pub fn _is_start_function(&self, full_name_map: &FullNameMap) -> bool {
        let input_types = &self.inputs;
        let mut flag = true;
        for ty in input_types {
            if !api_util::_is_end_type(&ty, full_name_map) {
                flag = false;
                break;
            }
        }
        flag
    }

    //TODO:判断一个函数是否是泛型函数
    pub fn _is_generic_function(&self) -> bool {
        let input_types = &self.inputs;
        for ty in input_types {
            if api_util::_is_generic_type(&ty) {
                return true;
            }
        }
        let output_type = &self.output;
        if let Some(ty) = output_type {
            if api_util::_is_generic_type(&ty) {
                return true;
            }
        }
        return false;
    }

    pub fn _has_no_output(&self) -> bool {
        match self.output {
            None => true,
            Some(_) => false,
        }
    }

    pub fn _pretty_print(&self, type_name_map: &TypeNameMap) -> String {
        let input_types = self.inputs.iter().map(|input_type| {
            type_full_name(input_type, type_name_map, TypeNameLevel::All)
        }).collect_vec().join(" ,");
        let output_type = if let Some(ref ty_) = self.output {
            format!(" -> {}", type_full_name(ty_, type_name_map, TypeNameLevel::All))
        } else {
            "".to_string()
        };
        format!("fn {}({}){}", self.full_name, input_types, output_type)
    }

    pub fn return_type_name(&self, type_name_map: &TypeNameMap) -> Option<String> {
        self.output.as_ref().and_then(|ty| Some(type_full_name(ty, type_name_map, super::type_name::TypeNameLevel::All)))
    }
}
