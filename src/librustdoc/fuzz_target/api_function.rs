use rustc_hir::{self,Mutability};
use crate::fuzz_target::api_util;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzzable_type::{self, FuzzableType};

use crate::clean;

#[derive(Debug,Clone,Copy,Hash,Eq, PartialEq,Ord, PartialOrd)]
pub enum ApiUnsafety {
    Unsafe,
    Normal,
}

#[derive(Clone, Debug)]
pub struct ApiFunction {
    pub full_name: String,//函数名，要来比较是否相等
    pub generics: clean::Generics,
    pub inputs: Vec<clean::Type>,
    pub output: Option<clean::Type>,
    pub _trait_full_path : Option<String>,//Trait的全限定路径,因为使用trait::fun来调用函数的时候，需要将trait的全路径引入
    pub _unsafe_tag: ApiUnsafety
}

impl ApiUnsafety {
    pub fn _get_unsafety_from_fnheader(fn_header:&rustc_hir::FnHeader)-> Self {
        let unsafety = fn_header.unsafety;
        match unsafety {
            rustc_hir::Unsafety::Unsafe => {
                ApiUnsafety::Unsafe
            }
            rustc_hir::Unsafety::Normal => {
                ApiUnsafety::Normal
            }
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
    pub fn _is_end_function(&self, full_name_map : &FullNameMap) -> bool {
        if self.contains_mut_borrow() {
            return false;
        }
        let return_type = &self.output;
        match return_type {
            Some(ty) => {
                if api_util::_is_end_type(&ty, full_name_map) {
                    return true;
                }else {
                    return false;
                }
            },
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
                clean::Type::BorrowedRef{mutability,..} | clean::Type::RawPointer(mutability,_) => {
                    if let Mutability::Mut = mutability {
                        return true;
                    }
                },
                _=> {}
            }
        }
        return false;
    }

    pub fn _is_start_function(&self, full_name_map : &FullNameMap) -> bool {
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

    

    pub fn _has_no_output(&self) -> bool{
        match self.output {
            None => true,
            Some(_) => false,
        }
    }

    pub fn _pretty_print(&self, full_name_map : &FullNameMap) -> String {
        let mut fn_line = format!("fn {}(", self.full_name);
        let input_len = self.inputs.len();
        for i in 0..input_len {
            let input_type = &self.inputs[i];
            if i != 0 {
                fn_line.push_str(" ,");
            }
            fn_line.push_str(api_util::_type_name(input_type, full_name_map).as_str());
        }
        fn_line.push_str(")");
        if let Some(ref ty_) = self.output {
            fn_line.push_str("->");
            fn_line.push_str(api_util::_type_name(ty_, full_name_map).as_str());
        }
        fn_line
    }

    pub fn filter_by_fuzzable_type(&self, full_name_map : &FullNameMap) -> bool {
        for input_ty_ in &self.inputs {
            if api_util::is_fuzzable_type(input_ty_, full_name_map) {
                let fuzzable_call_type = fuzzable_type::fuzzable_call_type(input_ty_, full_name_map);
                let (fuzzable_type, call_type) = fuzzable_call_type.generate_fuzzable_type_and_call_type();

                match &fuzzable_type {
                    FuzzableType::NoFuzzable => {
                        return true;
                    },
                    _ => {}
                }

                if fuzzable_type._is_multiple_dynamic_length() {
                    return true;
                }

                match &call_type {
                    CallType::_NotCompatible => {
                        return true;
                    },
                    _ => {}
                }
            }
        }
        return false;
    }
}