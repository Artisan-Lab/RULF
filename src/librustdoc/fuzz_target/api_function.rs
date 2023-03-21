use crate::clean;
use crate::formats::cache::Cache;
use crate::fuzz_target::api_util;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzzable_type::{self, FuzzableType};
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::type_name::{_type_name_with_def_id, only_public_type_name};
use crate::fuzz_target::type_name::{type_full_name, TypeNameLevel, TypeNameMap};
use itertools::Itertools;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::{self, Mutability};

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum ApiUnsafety {
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
    // 是否是辅助函数，辅助函数不计入覆盖率统计
    pub is_helper: bool,
}

impl ApiUnsafety {
    pub(crate) fn _get_unsafety_from_fnheader(fn_header: &rustc_hir::FnHeader) -> Self {
        match fn_header.unsafety {
            rustc_hir::Unsafety::Unsafe => ApiUnsafety::Unsafe,
            rustc_hir::Unsafety::Normal => ApiUnsafety::Normal,
        }
    }

    pub(crate) fn _is_unsafe(&self) -> bool {
        match self {
            ApiUnsafety::Unsafe => true,
            ApiUnsafety::Normal => false,
        }
    }
}

impl ApiFunction {
    pub(crate) fn _is_end_function(&self, type_name_map: &TypeNameMap, cache: &Cache) -> bool {
        if self.contains_mut_borrow() {
            return false;
        }
        let return_type = &self.output;
        match return_type {
            Some(ty) => api_util::_is_end_type(ty, type_name_map, cache),
            None => true,
        }
        //TODO:考虑可变引用或者是可变裸指针做参数的情况
    }

    pub(crate) fn contains_mut_borrow(&self) -> bool {
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

    pub(crate) fn is_defined_on_prelude_type(&self, prelude_types: &FxHashSet<String>) -> bool {
        let function_name_contains_prelude_type = prefixes.iter().any(|prelude_type| {
            let prelude_type_prefix = format!("{}::", prelude_type);
            self.full_name.starts_with(prelude_type_prefix.as_str())
        });
        let trait_contains_prelude_type = if let Some(ref trait_name) = self._trait_full_path {
            prefixes.iter().any(|prelude_type| {
                let prelude_type_prefix = format!("{}::", prelude_type);
                trait_name.starts_with(prelude_type_prefix.as_str())
            })
        } else {
            false
        };
        !function_name_contains_prelude_type & !trait_contains_prelude_type
    }

    pub(crate) fn _is_start_function(&self, type_name_map: &TypeNameMap, cache: &Cache) -> bool {
        let input_types = &self.inputs;
        let mut flag = true;
        for ty in input_types {
            if !api_util::_is_end_type(&ty, type_name_map, cache) {
                flag = false;
                break;
            }
        }
        flag
    }

    //TODO:判断一个函数是否是泛型函数
    pub(crate) fn _is_generic_function(&self) -> bool {
        !self.generics.is_empty()
    }

    pub(crate) fn _has_no_output(&self) -> bool {
        match self.output {
            None => true,
            Some(_) => false,
        }
    }

    pub fn _pretty_print(&self, type_name_map: &TypeNameMap) -> String {
        let input_types = self
            .inputs
            .iter()
            .map(|input_type| type_full_name(input_type, type_name_map, TypeNameLevel::All))
            .collect_vec()
            .join(" ,");
        let output_type = if let Some(ref ty_) = self.output {
            format!(" -> {}", type_full_name(ty_, type_name_map, TypeNameLevel::All))
        } else {
            "".to_string()
        };
        format!("fn {}({}){}", self.full_name, input_types, output_type)
    }

    pub fn _pretty_print_with_def_id(&self, type_name_map: &TypeNameMap) -> String {
        let input_types = self
            .inputs
            .iter()
            .map(|input_type| _type_name_with_def_id(input_type, type_name_map, TypeNameLevel::All))
            .collect_vec()
            .join(" ,");
        let output_type = if let Some(ref ty_) = self.output {
            format!(" -> {}", _type_name_with_def_id(ty_, type_name_map, TypeNameLevel::All))
        } else {
            "".to_string()
        };
        format!("fn {}({}){}", self.full_name, input_types, output_type)
    }

    pub fn return_type_name(&self, type_name_map: &TypeNameMap) -> Option<String> {
        self.output.as_ref().and_then(|ty| {
            Some(only_public_type_name(
                ty,
                type_name_map,
                crate::fuzz_target::type_name::TypeNameLevel::All,
            ))
        })
    }
}
