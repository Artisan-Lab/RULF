use crate::clean::{self, GenericBound, WherePredicate};
use crate::clean::{GenericParamDefKind, Generics};
use crate::clean::{Path, Type};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_util::{print_path,_type_name};
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::{api_function::ApiFunction, api_util};
use crate::fuzz_target::api_util::replace_lifetime;
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_span::symbol::Symbol;

use super::api_util::replace_type_with;

//impl From<FxHashSet<Def>>
#[derive(Clone)]
pub(crate) struct GenericFunction {
    pub(crate) api_function: ApiFunction,
    pub(crate) generic_map: GenericParamMap,
    pub(crate) bounded_symbols: FxHashSet<String>,
    impl_count: i32, // number of impl declaration
}

impl From<ApiFunction> for GenericFunction {
    fn from(mut api_function: ApiFunction) -> Self {
        replace_lifetime(&mut api_function);
        let mut gf = GenericFunction {
            api_function,
            generic_map: GenericParamMap::new(),
            bounded_symbols: FxHashSet::default(),
            impl_count: 0,
        };
        gf.resolve_argument_type();
        gf
    }
}

fn print_fact(facts: &Vec<Path>, cache:Option<&Cache>) -> String {
    facts.iter().map(|path| print_path(path, cache)).join(" + ")
}

impl GenericFunction {
    pub(crate) fn get_full_signature(&self, cache: &Cache) -> String {
        let mut signature = String::from("[G] fn ");
        let mut inputs = Vec::<String>::new();
        signature.push_str(&self.api_function.full_name);
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
            println!("{}: {}, ", name, print_fact(fact,Some(cache)));
        }
        println!("Type Pred:");
        for (type_, fact) in self.generic_map.type_pred.iter() {
            println!("{}: {}", _type_name(type_, Some(cache)), print_fact(fact, Some(cache)));
        }
        print!("bounded Params: ");
        for sym in &self.bounded_symbols {
            print!("{}, ", sym.as_str());
        }
        print!("\n");
        /* println!("=====\n");
        println!("{:?}\n",self.api_function.inputs);
        println!("{:?}\n",self.api_function.output);
        println!("=====\n"); */
    }

    pub(crate) fn add_generics(&mut self, generics: &Generics) {
        self.generic_map.add_generics(generics);
    }

    fn resolve_argument_type(&mut self) {
        self.resolve_impl_trait();
    }

    /* pub(crate) fn resolve_bounded_symbol(&mut self) {
        // println!("resolve bounded symbol: {}",self.api_function._pretty_print());
        for (key, bounds) in self.generic_map.iter() {
            if !bounds.is_empty() {
                self.bounded_symbols.insert(key.to_owned());
            }
        }

        let mut find_generic = |type_: &Type| -> Option<Type> {
            match type_ {
                Type::Generic(sym) => {
                    self.bounded_symbols.insert(sym.to_string());
                }
                _ => {}
            }
            None
        };

        for (type_, bounds) in self.generic_map.type_pred.iter() {
            // println!("{:?} : {:?}",type_,bounds);
            replace_type_with(type_, &mut find_generic);
            for bound in bounds.iter() {
                replace_type_with(&Type::Path { path: bound.clone() }, &mut find_generic);
            }
        }
        // println!("{:?}",self.bounded_symbols);
    } */

    fn resolve_impl_trait(&mut self) {
        // replace impl
        let mut input_vec = self.api_function.inputs.clone();
        //println!("before replace: {:?}\n", input_vec);
        for type_ in &mut input_vec {
            *type_ = self.replace_impl(type_);
        }
        //println!("after replace: {:?}\n", input_vec);
        self.api_function.inputs = input_vec;
        let output_type = self.api_function.output.clone();
        if let Some(type_) = output_type {
            self.api_function.output = Some(self.replace_impl(&type_));
        }
    }

    fn add_new_impl_generic(&mut self, bounds: &[GenericBound]) -> String {
        let generic_param_name = format!("impl_trait_{}", self.impl_count);
        self.impl_count += 1;
        self.generic_map.add_generic_bounds(&generic_param_name, bounds);
        generic_param_name
    }

    pub(crate) fn replace_impl(&mut self, ty: &clean::Type) -> clean::Type {
        if let Type::ImplTrait(bounds) = ty {
            let sym = self.add_new_impl_generic(&bounds);
            Type::Generic(Symbol::intern(&sym))
        } else if let Type::Generic(sym) = ty {
            ty.clone()
        } else {
            let mut new_ty = ty.clone();
            // If we meet nested type, travel all type
            match new_ty {
                clean::Type::Path { ref mut path } => {
                    for segment in path.segments.iter_mut() {
                        match segment.args {
                            clean::GenericArgs::AngleBracketed { ref mut args, .. } => {
                                for generic_arg in args.iter_mut() {
                                    if let clean::GenericArg::Type(ref mut inner_ty) = generic_arg {
                                        *inner_ty = self.replace_impl(inner_ty);
                                    }
                                }
                            }
                            clean::GenericArgs::Parenthesized {
                                ref mut inputs,
                                ref mut output,
                            } => {
                                for input_ty in inputs.iter_mut() {
                                    *input_ty = self.replace_impl(input_ty);
                                }
                                if let Some(output_ty) = output {
                                    **output_ty = self.replace_impl(&output_ty);
                                }
                            }
                        }
                    }
                }
                clean::Type::Tuple(ref mut types) => {
                    for ty_ in types {
                        *ty_ = self.replace_impl(ty_);
                    }
                }
                clean::Type::Slice(ref mut type_)
                | clean::Type::Array(ref mut type_, ..)
                | clean::Type::RawPointer(_, ref mut type_)
                | clean::Type::BorrowedRef { ref mut type_, .. } => {
                    *type_ = Box::new(self.replace_impl(type_));
                }
                _ => {}
            }
            new_ty
        }
    }
}
