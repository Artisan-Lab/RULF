use crate::clean::{self, GenericBound};
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::generic_type::{
    generic_bounds_contains_trait_with_generic, SimplifiedGenericBound,
};
use crate::fuzz_target::impl_util::where_preidicates_bounds_restrict_generic;
use crate::fuzz_target::type_name::TypeNameMap;
use crate::fuzz_target::type_util::{
    get_generics_of_clean_type, get_qpaths_in_clean_type, replace_types,
};
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::convert::TryFrom;
#[derive(Debug, Clone)]
pub struct GenericFunction {
    pub api_function: ApiFunction,
    pub generics: FxHashSet<String>,
    pub type_bounds: FxHashMap<clean::Type, SimplifiedGenericBound>,
    pub remaining_qpaths: FxHashSet<clean::Type>,
}

pub enum GenericFunctionError {
    // e.g. Option<T>: Debug
    RestricGenericBound,
    // internal error
    InternalError,
    // e.g. AsRef<S>, S
    TraitWithGeneric,
    // e.g. lifetime bound or Sized
    UnsupportedGenericBound,
}

impl TryFrom<ApiFunction> for GenericFunction {
    type Error = GenericFunctionError;
    fn try_from(api_function: ApiFunction) -> Result<Self, Self::Error> {
        let mut generic_function = GenericFunction {
            api_function,
            generics: FxHashSet::default(),
            type_bounds: FxHashMap::default(),
            remaining_qpaths: FxHashSet::default(),
        };
        generic_function.collect_generics();
        if where_preidicates_bounds_restrict_generic(&generic_function.api_function.generics) {
            return Err(GenericFunctionError::RestricGenericBound);
        }
        if !generic_function.check_generics() {
            return Err(GenericFunctionError::InternalError);
        }

        if generic_function.contains_trait_with_generic() {
            return Err(GenericFunctionError::TraitWithGeneric);
        }

        if generic_function.contains_unsupported_generic_bound() {
            return Err(GenericFunctionError::UnsupportedGenericBound);
        }

        generic_function.collect_simplified_generic_bounds();
        generic_function.collect_remaining_qpath();
        Ok(generic_function)
    }
}

impl GenericFunction {
    fn collect_generics(&mut self) {
        let mut generics = FxHashSet::default();
        self.api_function.inputs.iter().for_each(|type_| {
            generics.extend(get_generics_of_clean_type(type_));
        });
        self.api_function.output.iter().for_each(|type_| {
            generics.extend(get_generics_of_clean_type(type_));
        });
        self.generics = generics;
    }

    /// collect qpath that relies on some generic
    fn collect_remaining_qpath(&mut self) {
        let mut remaining_qpath = FxHashSet::default();
        self.api_function.inputs.iter().for_each(|type_| {
            remaining_qpath.extend(get_qpaths_in_clean_type(type_));
        });
        self.api_function.output.iter().for_each(|type_| {
            remaining_qpath.extend(get_qpaths_in_clean_type(type_));
        });
        self.remaining_qpaths = remaining_qpath;
    }

    fn check_generics(&self) -> bool {
        self.generics.iter().for_each(|generic| {
            let contains_generic_def = self
                .api_function
                .generics
                .params
                .iter()
                .any(|generic_param_def| generic_param_def.name == *generic);
            if !contains_generic_def {
                error!("{} in {} does not have definition.", self.api_function.full_name, generic);
            }
        });

        self.generics.iter().all(|generic| {
            self.api_function
                .generics
                .params
                .iter()
                .any(|generic_param_def| generic_param_def.name == *generic)
        })
    }

    fn contains_trait_with_generic(&self) -> bool {
        let clean::Generics { params, where_predicates } = self.api_function.generics.clone();
        let params_contains_trait_with_generic = params.iter().any(|generic_param_def| {
            if let Some(bounds) = generic_param_def.get_bounds() {
                generic_bounds_contains_trait_with_generic(bounds)
            } else {
                false
            }
        });

        let where_predicates_contains_trait_with_generic =
            where_predicates.iter().any(|where_predicate| {
                if let Some(bounds) = where_predicate.get_bounds() {
                    generic_bounds_contains_trait_with_generic(bounds)
                } else {
                    false
                }
            });

        params_contains_trait_with_generic | where_predicates_contains_trait_with_generic
    }

    fn contains_unsupported_generic_bound(&self) -> bool {
        let clean::Generics { params, where_predicates } = self.api_function.generics.to_owned();
        let unsupported_param_bounds = params.iter().any(|generic_param_def| {
            if let Some(bounds) = generic_param_def.get_bounds() {
                if let Err(_) = SimplifiedGenericBound::try_from(bounds) {
                    return true;
                }
            }
            false
        });
        let unsupported_where_predicate_bounds = where_predicates.iter().any(|where_predicate| {
            if let clean::WherePredicate::BoundPredicate { bounds, .. } = where_predicate {
                if let Err(_) = SimplifiedGenericBound::try_from(&bounds[..]) {
                    return true;
                }
            }
            false
        });
        unsupported_param_bounds | unsupported_where_predicate_bounds
    }

    fn collect_simplified_generic_bounds(&mut self) {
        let clean::Generics { params, where_predicates } = self.api_function.generics.to_owned();
        params.iter().for_each(|generic_param_def| {
            let bounded_generic = clean::Type::Generic(generic_param_def.name.clone());
            if let Some(bounds) = generic_param_def.get_bounds() {
                self.push_one_type_bounds(bounds, bounded_generic);
            }
        });
        where_predicates.iter().for_each(|where_predicate| {
            if let clean::WherePredicate::BoundPredicate { ty, bounds, .. } = where_predicate {
                self.push_one_type_bounds(bounds, ty.to_owned());
            }
        })
    }

    fn collect_opaque_types(&self) -> FxHashMap<clean::Type, SimplifiedGenericBound> {
        let mut opaque_types = FxHashMap::default();
        self.api_function.inputs.iter().for_each(|input_ty| {
            if let clean::Type::ImplTrait(bounds) = input_ty {
                if !generic_bounds_contains_trait_with_generic(bounds) {
                    if let Ok(simplified_bound) =
                        SimplifiedGenericBound::try_from(bounds.as_slice())
                    {
                        opaque_types.insert(input_ty.to_owned(), simplified_bound);
                    }
                }
            }
        });
        opaque_types
    }

    fn push_one_type_bounds(&mut self, bounds: &[GenericBound], bounded_type: clean::Type) {
        let simplified_bound = SimplifiedGenericBound::try_from(bounds).unwrap();
        if self.type_bounds.contains_key(&bounded_type) {
            let old_generic_bound = self.type_bounds.get_mut(&bounded_type).unwrap();
            old_generic_bound.merge_other_bound(simplified_bound);
        } else {
            self.type_bounds.insert(bounded_type, simplified_bound);
        }
    }

    pub fn contains_empty_bounds(&self) -> bool {
        self.type_bounds.iter().any(|(_, bounds)| bounds.is_empty())
    }

    pub fn try_monomorphize(
        &self,
        types: &FxHashMap<DefId, clean::Type>,
        type_name_map: &TypeNameMap,
        traits_of_type: &FxHashMap<DefId, FxHashSet<clean::Type>>,
        known_bounds: &mut Vec<SimplifiedGenericBound>,
        bound_type_map: &mut FxHashMap<usize, clean::Type>,
        failed_bounds: &mut FxHashSet<usize>,
        primitive_types: &mut usize,
        convert_traits: &mut usize,
        defined_types: &mut usize,
        global_replace_map: &mut FxHashMap<clean::Type, clean::Type>,
    ) -> Result<ApiFunction, ()> {
        let mut replace_map = FxHashMap::default();
        self.type_bounds.iter().for_each(|(type_, bound)| {
            if bound.is_empty() {
                // if this is an empty bounds
                if global_replace_map.contains_key(type_) {
                    let replace_type = global_replace_map.get(type_).unwrap().to_owned();
                    replace_map.insert(type_.to_owned(), replace_type);
                } else {
                    let replace_type = SimplifiedGenericBound::default_type_for_empty_bounds();
                    replace_map.insert(type_.to_owned(), replace_type);
                }
            } else if let Some(index) = index_of(known_bounds, bound) {
                // the bound is one of known bounds
                if bound_type_map.contains_key(&index) {
                    let replace_type = bound_type_map.get(&index).unwrap();
                    replace_map.insert(type_.to_owned(), replace_type.to_owned());
                }
            } else {
                known_bounds.push(bound.to_owned());
                let index = known_bounds.len() - 1;
                if let Some(replace_type) =
                    bound.can_be_some_type(types, type_name_map, traits_of_type)
                {
                    replace_map.insert(type_.to_owned(), replace_type.to_replace_type());
                    bound_type_map.insert(index, replace_type.to_replace_type());
                    global_replace_map.insert(type_.to_owned(), replace_type.to_replace_type());
                    if replace_type.is_primitive_type() {
                        *primitive_types += 1;
                    } else if replace_type.is_convert_trait() {
                        *convert_traits += 1;
                    } else if replace_type.is_defined_type() {
                        *defined_types += 1;
                    }
                } else {
                    failed_bounds.insert(index);
                }
            }
        });
        if self.can_be_fully_monomorphized(&replace_map) {
            let opaque_replace_map =
                self.get_opaque_replace_map(types, type_name_map, traits_of_type);
            return Ok(self.monomorphize(&replace_map, &opaque_replace_map));
        } else {
            return Err(());
        }
    }

    pub fn can_be_fully_monomorphized(
        &self,
        replace_map: &FxHashMap<clean::Type, clean::Type>,
    ) -> bool {
        let generic_fully_monomorphized = self.generics.iter().all(|generic| {
            replace_map.iter().any(|(type_, ..)| {
                if let clean::Type::Generic(generic_name) = type_ {
                    *generic_name == *generic
                } else {
                    false
                }
            })
        });
        let remaining_qpath_fully_monomorphized = self
            .remaining_qpaths
            .iter()
            .all(|remaining_qpath| replace_map.contains_key(remaining_qpath));
        generic_fully_monomorphized & remaining_qpath_fully_monomorphized
    }

    /// 判断一个泛型函数是否需要对返回类型进行标注。判断的依据是，存在某个泛型参数，在返回类型中出现，但没有在参数中出现
    pub fn should_notate_return_type(&self) -> bool {
        let return_type_generics = self
            .api_function
            .output
            .as_ref()
            .map_or(FxHashSet::default(), |output_ty| get_generics_of_clean_type(&output_ty));
        let input_type_generics =
            self.api_function.inputs.iter().fold(FxHashSet::default(), |mut former, ty| {
                former.extend(get_generics_of_clean_type(ty));
                former
            });
        return_type_generics.iter().any(|generic| !input_type_generics.contains(generic))
    }

    pub fn monomorphize(
        &self,
        replace_map: &FxHashMap<clean::Type, clean::Type>,
        opaque_replace_map: &FxHashMap<clean::Type, clean::Type>,
    ) -> ApiFunction {
        let ApiFunction {
            full_name,
            mut generics,
            inputs,
            output,
            _trait_full_path,
            _unsafe_tag,
            is_helper,
            ..
        } = self.api_function.clone();
        generics.params.clear();
        generics.where_predicates.clear();
        let mut inputs =
            inputs.into_iter().map(|type_| replace_types(&type_, replace_map)).collect_vec();
        // replace opaque types in input types
        inputs =
            inputs.into_iter().map(|type_| replace_types(&type_, opaque_replace_map)).collect_vec();
        let output = output.and_then(|type_| Some(replace_types(&type_, replace_map)));
        let return_type_notation = self.should_notate_return_type();
        if return_type_notation {
            debug!("{} needs return type notation.", full_name);
        }
        ApiFunction {
            full_name,
            generics,
            inputs,
            output,
            _trait_full_path,
            _unsafe_tag,
            return_type_notation,
            is_helper,
        }
    }

    fn get_opaque_replace_map(
        &self,
        types: &FxHashMap<DefId, clean::Type>,
        type_name_map: &TypeNameMap,
        traits_of_type: &FxHashMap<DefId, FxHashSet<clean::Type>>,
    ) -> FxHashMap<clean::Type, clean::Type> {
        let opaque_types = self.collect_opaque_types();
        let mut opaque_replace_map = FxHashMap::default();
        for (opaque_type, bounds) in opaque_types.iter() {
            if let Some(replace_type) =
                bounds.can_be_some_type(types, type_name_map, traits_of_type)
            {
                opaque_replace_map.insert(opaque_type.to_owned(), replace_type.to_replace_type());
            }
        }
        opaque_replace_map
    }
}

fn index_of<T: PartialEq + Eq + Clone>(vec: &Vec<T>, item: &T) -> Option<usize> {
    for i in 0..vec.len() {
        if *(vec.get(i).unwrap()) == *item {
            return Some(i);
        }
    }
    None
}
