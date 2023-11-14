use crate::clean::{self, GenericBound, WherePredicate};
use crate::clean::{GenericParamDefKind, Generics};
use crate::clean::{Path, Type};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_util::{_type_name, print_path};
use crate::fuzz_target::api_util::{print_fact, replace_lifetime};
use crate::fuzz_target::api_util::{replace_type_with, scan_type_with};
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::{api_function::ApiFunction, api_util};
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_span::symbol::Symbol;

//impl From<FxHashSet<Def>>
#[derive(Clone)]
pub(crate) struct GenericFunction {
    pub(crate) api_function: ApiFunction,
    pub(crate) generic_map: GenericParamMap,
    impl_count: i32, // number of impl declaration
}

impl From<ApiFunction> for GenericFunction {
    fn from(mut api_function: ApiFunction) -> Self {
        replace_lifetime(&mut api_function);
        let mut gf =
            GenericFunction { api_function, generic_map: GenericParamMap::new(), impl_count: 0 };
        gf.resolve_argument_type();
        gf
    }
}

impl GenericFunction {
    pub(crate) fn get_full_signature(&self, cache: &Cache) -> String {
        let mut signature = String::new();
        if !self.is_solvable() {
            signature.push_str("*");
        }
        signature.push_str("fn ");
        let mut inputs = Vec::<String>::new();
        signature.push_str(&self.api_function.full_name(cache));
        for ty in self.api_function.inputs.iter() {
            inputs.push(api_util::_type_name(ty, Some(cache)));
        }
        signature.push_str("(");
        signature.push_str(inputs.join(", ").as_str());
        signature.push_str(") -> ");
        if let Some(ref ty) = self.api_function.output {
            signature.push_str(api_util::_type_name(ty, Some(cache)).as_str());
        } else {
            signature.push_str("void");
        }
        signature
    }

    pub(crate) fn pretty_print(&self, cache: &Cache) {
        println!("{}", self.get_full_signature(cache));
        println!("Where:");
        for (name, fact) in self.generic_map.iter() {
            println!("{}: {}, ", name, print_fact(fact, Some(cache)));
        }
        println!("Type Pred:");
        for (type_, fact) in self.generic_map.type_pred.iter() {
            println!("{}: {}", _type_name(type_, Some(cache)), print_fact(fact, Some(cache)));
        }
        print!("\n");
        /* println!("=====\n");
        println!("{:?}\n",self.api_function.inputs);
        println!("{:?}\n",self.api_function.output);
        println!("=====\n"); */
    }

    pub(crate) fn set_self_type(&mut self, self_type: &Type) {
        self.generic_map.set_self_type(self_type);
    }

    pub(crate) fn add_generics(&mut self, generics: &Generics, ignore: Option<String>) {
        self.generic_map.add_generics(generics, ignore);
    }

    pub(crate) fn is_solvable(&self) -> bool {
        let mut have_unknown_generic = false;
        let mut check = |type_: &Type| -> bool {
            if let Type::Generic(sym) = type_ {
                for defname in self.generic_map.generic_defs.iter() {
                    if defname == sym.as_str() {
                        return false;
                    }
                }
                println!("unknown generic: {:?}", sym);
                have_unknown_generic = true;
                return false;
            }
            true
        };

        for input in self.api_function.inputs.iter() {
            scan_type_with(input, &mut check);
        }

        if let Some(ref output) = self.api_function.output {
            scan_type_with(output, &mut check);
        }

        if have_unknown_generic {
            return false;
        }

        return self.generic_map.is_solvable();
    }

    fn resolve_argument_type(&mut self) {
        self.resolve_impl_trait();
    }

    fn resolve_impl_trait(&mut self) {
        let mut input_vec = self.api_function.inputs.clone();
        let mut output_type = self.api_function.output.clone();

        let mut replace_impl = |type_: &mut Type| -> bool {
            if let Type::ImplTrait(ref bounds) = type_ {
                let sym = self.add_new_impl_generic(bounds);
                *type_ = Type::Generic(Symbol::intern(&sym));
                return false;
            }
            return true;
        };
        
        for type_ in input_vec.iter_mut() {
            replace_type_with(type_, &mut replace_impl);
        }

        if let Some(ref mut output) = output_type {
            replace_type_with(output, &mut replace_impl);
        }
        self.api_function.inputs = input_vec;
        self.api_function.output = output_type;
    }

    fn add_new_impl_generic(&mut self, bounds: &[GenericBound]) -> String {
        let generic_param_name = format!("ImplTrait{}", self.impl_count);
        self.impl_count += 1;
        self.generic_map.add_generic_bounds(&generic_param_name, bounds);
        generic_param_name
    }
}
