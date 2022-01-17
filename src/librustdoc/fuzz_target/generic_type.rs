use std::collections::{HashSet, HashMap};
use itertools::Itertools;
use rustc_hir::def_id::DefId;

use crate::clean::{self, GenericBound, GetDefId};

// FIXME: Why these are not marker from std?. 
pub static PRIMITIVE_TRAITS: [&'static str; 10] = ["core::cmp::Ord", 
                                                  "core::cmp::PartialEq",
                                                  "core::clone::Clone", 
                                                  "core::marker::Copy", 
                                                  "core::hash::Hash",
                                                  "core::fmt::Display",
                                                  "core::cmp::PartialOrd",
                                                  "core::cmp::Eq",
                                                  "core::fmt::Debug",
                                                  "core::default::Default"];

/// This represents generic bound without `trait with generic`
#[derive(Debug, Clone)]
pub struct SimplifiedGenericBound {
    trait_bounds: HashSet<clean::Type>,
}

impl From<&[GenericBound]> for SimplifiedGenericBound {
    fn from(bounds: &[GenericBound]) -> Self {
        let trait_bounds = bounds.iter().filter(|generic_bound| {
            if let GenericBound::TraitBound(_, trait_bound_modifier) = generic_bound {
                // FIXME: We skip ?Sized bound here.
                // ?Sized is the only case that the modifier is not None currently.
                *trait_bound_modifier == rustc_hir::TraitBoundModifier::None
            } else {
                false
            }
        }).map(|generic_bound| {
            if let GenericBound::TraitBound(poly_trait,..) = generic_bound {
                poly_trait.trait_.clone()
            } else {
                unreachable!("Lifetime bounds should be already filtered. Internal Error.");
            }
        }).collect();
        SimplifiedGenericBound { trait_bounds }
    }
}

impl SimplifiedGenericBound {
    pub fn merge_other_bound(&mut self, other_bound: SimplifiedGenericBound) {
        self.trait_bounds.extend(other_bound.trait_bounds);
    }

    // determine whether a bound can be a primitive type
    pub fn can_be_primitive_type(&self, trait_name_map: &HashMap<DefId, String>) -> bool {
        // FIXME: This is a very naive implementation. We only compare if trait names are equal.
        self.trait_bounds.iter().all(|trait_bound| {
            // Safety: trait should always has a def_id, otherwise is a fatal error
            let trait_def_id = trait_bound.def_id().unwrap();
            // Safety: trait name should in trait name map
            let trait_name = trait_name_map.get(&trait_def_id).unwrap().to_owned();
            // This is 
            PRIMITIVE_TRAITS.iter().any(|primitive_trait| *primitive_trait == &trait_name)
        })
    }

    pub fn _format_string_(&self, trait_name_map: &HashMap<DefId, String>) -> String {
        let res = self.trait_bounds.iter().map(|trait_bound| {
            let trait_def_id = trait_bound.def_id().unwrap();
            trait_name_map.get(&trait_def_id).unwrap().to_owned()
        }).collect_vec();
        res.join(",")
    }

    pub fn can_be_replaced_with_type(&self, types: &HashMap<DefId, clean::Type>, traits_of_type: &HashMap<DefId, HashSet<clean::Type>>) -> Option<clean::Type> {
        for (def_id, type_) in types {
            if let Some(traits) = traits_of_type.get(def_id) {
                let all_traits_satisified = self.trait_bounds.iter().all(|trait_bound| {
                    // FIXME: This only check whether trait points to the same type
                    // We don't care about trait generics here
                    traits.iter().any(|trait_| trait_.def_id() == trait_bound.def_id())
                });
                if all_traits_satisified {
                    return Some(type_.to_owned());
                }
            } else {
                // The type has no bounds. This should be dead code. Since we replace these types with primitives
                if self.trait_bounds.len() == 0 {
                    return Some(type_.to_owned());
                }
            }
        }
        None
    }
}

/// Test whether generic bounds contains trait with generic
pub fn generic_bounds_contains_trait_with_generic(bounds: &[GenericBound]) -> bool {
    bounds.iter().any(|generic_bound| {
        if let Some(poly_trait) = generic_bound.get_poly_trait() {
            trait_contains_generic(&poly_trait)
        } else {
            false
        }
    })
}

/// The trait itself has generic params
/// We currently skip APIs with such traits.
pub fn trait_contains_generic(poly_trait: &clean::PolyTrait) -> bool {
    poly_trait.generic_params.len() != 0
}

fn _trait_name_(trait_: &clean::Type, trait_name_map: &HashMap<DefId, String>) -> String {
    let trait_did = trait_.def_id().unwrap();
    trait_name_map.get(&trait_did).unwrap().to_owned()
}