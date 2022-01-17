use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::clean::{self, GenericBound};

use super::api_function::ApiFunction;
use super::impl_util::where_preidicates_bounds_restrict_generic;
use super::type_util::{get_qpaths_in_clean_type, get_generics_of_clean_type, replace_types};
use super::generic_type::{generic_bounds_contains_trait_with_generic, SimplifiedGenericBound};

#[derive(Debug, Clone)]
pub struct GenericFunction {
    pub api_function: ApiFunction,
    pub generics: HashSet<String>,
    pub type_bounds: HashMap<clean::Type, SimplifiedGenericBound>,
    pub remaining_qpaths: HashSet<clean::Type>,
    // pub generic_substitute: HashMap<String, clean::Type>,
    // pub qpath_substitute: HashMap<clean::Type, clean::Type>,
}

impl GenericFunction {
    pub fn from_api_function(api_function: ApiFunction) -> Option<Self> {
        let mut generic_function = GenericFunction { 
            api_function, 
            generics: HashSet::new(),
            type_bounds: HashMap::new(),
            remaining_qpaths: HashSet::new(),
        };
        if where_preidicates_bounds_restrict_generic(&generic_function.api_function.generics) {
            println!("FIXME(where bound for function): {}", generic_function.api_function.full_name);
        }
        generic_function.collect_generics();
        if !generic_function.check_generics() || generic_function.contains_trait_with_generic(){
            return None;
        }
        generic_function.collect_simplified_generic_bounds();
        generic_function.collect_remaining_qpath();
        Some(generic_function)
    }

    fn collect_generics(&mut self) {
        let mut generics = HashSet::new();
        self.api_function.inputs.iter().for_each(|type_| {
            generics.extend(get_generics_of_clean_type(type_));
        });
        self.api_function.output.iter().for_each(|type_| {
            generics.extend(get_generics_of_clean_type(type_));
        });
        self.generics = generics;
    }

    /// collect qpath that is not 
    fn collect_remaining_qpath(&mut self) {
        let mut remaining_qpath = HashSet::new();
        self.api_function.inputs.iter().for_each(|type_| {
            remaining_qpath.extend(get_qpaths_in_clean_type(type_));
        });
        self.api_function.output.iter().for_each(|type_| {
            remaining_qpath.extend(get_qpaths_in_clean_type(type_));
        });
        self.remaining_qpaths = remaining_qpath;
    }

    fn check_generics(&self) -> bool{
        self.generics.iter().for_each(|generic| {
            let contains_generic_def= self.api_function.generics.params.iter().any(|generic_param_def| {
                generic_param_def.name == *generic
            });
            if !contains_generic_def{
                println!("{} in {} does not have definition.", self.api_function.full_name, generic);
            }
        });

        self.generics.iter().all(|generic| {
            self.api_function.generics.params.iter().any(|generic_param_def| {
                generic_param_def.name == *generic
            })
        })
    }

    fn contains_trait_with_generic(&self) -> bool {
        let clean::Generics {params, where_predicates} = self.api_function.generics.clone();
        let params_contains_trait_with_generic = params.iter().any(|generic_param_def| { 
            if let Some(bounds) = generic_param_def.get_bounds() {
                generic_bounds_contains_trait_with_generic(bounds)
            } else {
                false
            }
        });

        let where_predicates_contains_trait_with_generic = where_predicates.iter().any(|where_predicate| {
            if let Some(bounds) = where_predicate.get_bounds() {
                generic_bounds_contains_trait_with_generic(bounds)
            } else {
                false
            }
        });

        params_contains_trait_with_generic | where_predicates_contains_trait_with_generic
    }

    fn collect_simplified_generic_bounds(&mut self) {
        let clean::Generics{params, where_predicates} = self.api_function.generics.to_owned();
        params.iter().for_each(|generic_param_def| {
            let bounded_generic = clean::Type::Generic(generic_param_def.name.clone());
            if let Some(bounds) = generic_param_def.get_bounds() {
                self.push_one_tyoe_bounds(bounds, bounded_generic);
            }
        });
        where_predicates.iter().for_each(|where_predicate| {
            if let clean::WherePredicate::BoundPredicate{ty, bounds} = where_predicate {
                self.push_one_tyoe_bounds(bounds, ty.to_owned());
            }
        })
    }

    fn push_one_tyoe_bounds(&mut self, bounds: &[GenericBound], bounded_type: clean::Type) {
        let simplified_bound = SimplifiedGenericBound::from(bounds);
        if self.type_bounds.contains_key(&bounded_type) {
            let old_generic_bound = self.type_bounds.get_mut(&bounded_type).unwrap();
            old_generic_bound.merge_other_bound(simplified_bound);
        } else {
            self.type_bounds.insert(bounded_type, simplified_bound);
        }
    }

    pub fn can_be_fully_monomorphized(&self, replace_map: &HashMap<clean::Type, clean::Type>) -> bool {
        let generic_fully_monomorphized = self.generics.iter().all(|generic| {
            replace_map.iter().any(|(type_, ..)| {
                if let clean::Type::Generic(generic_name) = type_ {
                    *generic_name == *generic
                } else {
                    false
                }
            })
        });
        let remaining_qpath_fully_monomorphized= self.remaining_qpaths.iter().all(|remaining_qpath| {
            replace_map.contains_key(remaining_qpath)
        });
        generic_fully_monomorphized & remaining_qpath_fully_monomorphized
    }

    pub fn monomorphize(&self, replace_map: &HashMap<clean::Type, clean::Type>) -> ApiFunction {
        // println!("monomorphize {}.", self.api_function.full_name);
        let ApiFunction { full_name, mut generics, inputs, output, _trait_full_path, _unsafe_tag } = self.api_function.clone();
        generics.params.clear();
        generics.where_predicates.clear();
        let inputs = inputs.into_iter().map(|type_| {
            replace_types(&type_, replace_map)
        }).collect_vec();
        let output = output.and_then(|type_| Some(replace_types(&type_, replace_map)));
        ApiFunction {
            full_name,
            generics,
            inputs,
            output,
            _trait_full_path,
            _unsafe_tag,
        }
    }
}

