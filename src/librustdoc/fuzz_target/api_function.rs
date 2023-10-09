use crate::clean;
use crate::formats::cache::Cache;
use crate::fuzz_target::api_util;
use crate::fuzz_target::api_util::{is_unsupported_fuzzable,_type_name};
use crate::fuzz_target::api_util::scan_type_with;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzzable_type::{self, FuzzableType};
use crate::fuzz_target::impl_util::FullNameMap;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::{self, Mutability};
use crate::clean::Type;

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum ApiUnsafety {
    Unsafe,
    Normal,
}

#[derive(Clone, Debug)]
pub(crate) struct ApiFunction {
    //pub(crate) full_name: String, //函数名，要来比较是否相等
    pub(crate) name: String,
    pub(crate) full_path: String,
    pub(crate) inputs: Vec<Type>,
    pub(crate) output: Option<Type>,
    pub(crate) self_: Option<Type>,
    pub(crate) trait_: Option<Type>, //Trait的全限定路径,因为使用trait::fun来调用函数的时候，需要将trait的全路径引入
    pub(crate) _unsafe_tag: ApiUnsafety,
    pub(crate) local: bool,
    pub(crate) mono: bool,
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
    pub(crate) fn full_name(&self, cache: &Cache) -> String{
        match (&self.self_, &self.trait_){
            (None,None) => format!("{}",self.full_path),
            (Some(self_), None) => format!("{}::{}",_type_name(&self_,Some(cache)),self.name),
            (None, Some(trait_)) => format!("{}::{}",_type_name(&trait_,Some(cache)),self.name),
            (Some(self_),Some(trait_)) => format!("<{} as {}>::{}",_type_name(&self_,Some(cache)),_type_name(&trait_,Some(cache)),self.name)
        }
    }
    pub(crate) fn is_mono(&self) -> bool {
        self.mono
    }

    pub(crate) fn is_local(&self) -> bool {
        self.local
    }

    pub(crate) fn _is_end_function(&self, full_name_map: &FullNameMap, cache: &Cache) -> bool {
        if self.contains_mut_borrow() {
            return false;
        }
        let return_type = &self.output;
        match return_type {
            Some(ty) => {
                if api_util::_is_end_type(&ty, full_name_map, cache) {
                    return true;
                } else {
                    return false;
                }
            }
            None => true,
        }
        //TODO:考虑可变引用或者是可变裸指针做参数的情况
    }

    /*  pub(crate) fn is_mono(&self) -> bool{
           self.mono
       }
    */
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

    pub(crate) fn is_unsupported(&self) -> bool {
        let mut success = true;
        let mut check = |type_: &Type| -> bool {
            match type_ {
                Type::Generic(..) | Type::DynTrait { .. } | Type::QPath { .. } => {
                    success = false;
                }
                _ => {}
            }
            success
        };

        for input in self.inputs.iter() {
            scan_type_with(input, &mut check);
        }

        if let Some(ref output) = self.output {
            scan_type_with(output, &mut check);
        }

        success
    }

   /*  pub(crate) fn is_defined_on_prelude_type(&self, prelude_types: &FxHashSet<String>) -> bool {
        let function_name_contains_prelude_type =
            prelude_types.iter().any(|prelude_type| self.full_name.starts_with(prelude_type));
        let trait_contains_prelude_type = if let Some(ref trait_name) = self._trait_full_path {
            prelude_types.iter().any(|prelude_type| trait_name.starts_with(prelude_type))
        } else {
            false
        };
        !function_name_contains_prelude_type & !trait_contains_prelude_type
    } */

    pub(crate) fn _is_start_function(&self, full_name_map: &FullNameMap, cache: &Cache) -> bool {
        let input_types = &self.inputs;
        let mut flag = true;
        for ty in input_types {
            if !api_util::_is_end_type(&ty, full_name_map, cache) {
                flag = false;
                break;
            }
        }
        flag
    }

    pub(crate) fn _has_no_output(&self) -> bool {
        match self.output {
            None => true,
            Some(_) => false,
        }
    }

    pub(crate) fn _pretty_print(&self, cache: &Cache) -> String {
        let mut fn_line =
            format!("fn {}{}(", self.full_name(cache), if self.is_mono() { "#mono" } else { "" });
        let input_len = self.inputs.len();
        for i in 0..input_len {
            let input_type = &self.inputs[i];
            if i != 0 {
                fn_line.push_str(", ");
            }
            fn_line.push_str(api_util::_type_name(input_type, Some(cache)).as_str());
        }
        fn_line.push_str(")");

        if let Some(ref ty_) = self.output {
            fn_line.push_str(" -> ");
            fn_line.push_str(api_util::_type_name(ty_, Some(cache)).as_str());
        }
        fn_line
    }

    pub(crate) fn contains_unsupported_fuzzable_type(
        &self,
        full_name_map: &FullNameMap,
        cache: &Cache,
    ) -> bool {
        for input_ty_ in &self.inputs {
            if is_unsupported_fuzzable(input_ty_,full_name_map,cache){
                return true;
            }
            /* let fuzzable_call_type =
                fuzzable_type::fuzzable_call_type(input_ty_, full_name_map, cache);

            if !fuzzable_call_type.is_fuzzable() {
                continue;
            }

            let (fuzzable_type, call_type) =
                fuzzable_call_type.generate_fuzzable_type_and_call_type();

            if !fuzzable_type.is_fuzzable() {
                println!("input fail#0: {}", _type_name(input_ty_, Some(cache)));
                return true;
            }

            if fuzzable_type._is_multiple_dynamic_length() {
                println!("input fail#1");
                return true;
            }

            if !call_type.is_compatible() {
                println!("input fail#2");
                return true;
            } */
        }
        return false;
    }
}
