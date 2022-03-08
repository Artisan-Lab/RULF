use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_hir::Mutability;
use std::{
    collections::{HashMap, HashSet},
    convert::TryFrom,
};

use crate::clean::{self, GenericBound};

use super::type_name::{type_full_name, type_name, TypeNameLevel, TypeNameMap};
use super::type_util::extract_as_ref;

// FIXME: Why these are not marker from std?.
pub static PRIMITIVE_TRAITS: [&'static str; 10] = [
    "core::cmp::Ord",
    "core::cmp::PartialEq",
    "core::clone::Clone",
    "core::marker::Copy",
    "core::hash::Hash",
    "core::fmt::Display",
    "core::cmp::PartialOrd",
    "core::cmp::Eq",
    "core::fmt::Debug",
    "core::default::Default",
];
// FIXME: u8 slice cannot contain write trait(Temporary use)
pub static U8_SLICE_TRAITS: [&'static str; 1] = ["std::io::Read"];
// FIXME：仅仅是为clap库所暂时使用的
pub static STR_SLICE_TRAITS: [&'static str; 1] = ["core::convert::AsRef<Str>"];

#[derive(Debug, Clone, Copy)]
pub enum GenericBoundError {
    Lifetime,
    Sized,
}

/// This represents generic bound without `trait with generic`
#[derive(Debug, Clone)]
pub struct SimplifiedGenericBound {
    trait_bounds: HashSet<clean::Type>,
}

impl TryFrom<&[GenericBound]> for SimplifiedGenericBound {
    type Error = GenericBoundError;
    fn try_from(bounds: &[GenericBound]) -> Result<Self, Self::Error> {
        for generic_bound in bounds.iter() {
            if let GenericBound::TraitBound(_, trait_bound_modifier) = generic_bound {
                if !(*trait_bound_modifier == rustc_hir::TraitBoundModifier::None) {
                    return Err(GenericBoundError::Sized);
                }
            } else {
                return Err(GenericBoundError::Lifetime);
            }
        }

        let trait_bounds = bounds
            .iter()
            .map(|generic_bound| {
                if let GenericBound::TraitBound(poly_trait, ..) = generic_bound {
                    poly_trait.trait_.clone()
                } else {
                    unreachable!("Lifetime bounds should be already filtered. Internal Error.");
                }
            })
            .collect();
        Ok(SimplifiedGenericBound { trait_bounds })
    }
}

impl SimplifiedGenericBound {
    pub fn merge_other_bound(&mut self, other_bound: SimplifiedGenericBound) {
        self.trait_bounds.extend(other_bound.trait_bounds);
    }

    // determine whether a bound can be a primitive type
    pub fn can_be_primitive_type(&self, type_name_map: &TypeNameMap) -> bool {
        // FIXME: This is a very naive implementation. We only compare if trait names are equal.
        self.trait_bounds.iter().all(|trait_bound| {
            let trait_name = type_full_name(trait_bound, type_name_map, TypeNameLevel::All);
            PRIMITIVE_TRAITS.iter().any(|primitive_trait| *primitive_trait == &trait_name)
        })
    }

    pub fn can_be_u8_slice(&self, type_name_map: &TypeNameMap) -> bool {
        self.trait_bounds.iter().all(|trait_bound| {
            let trait_name = type_full_name(trait_bound, type_name_map, TypeNameLevel::All);
            U8_SLICE_TRAITS.iter().any(|primitive_trait| *primitive_trait == &trait_name)
        })
    }

    pub fn can_be_str_slice(&self, type_name_map: &TypeNameMap) -> bool {
        self.trait_bounds.iter().all(|trait_bound| {
            let trait_name = type_full_name(trait_bound, type_name_map, TypeNameLevel::All);
            STR_SLICE_TRAITS.iter().any(|primitive_trait| *primitive_trait == &trait_name)
        })
    }

    pub fn is_as_ref_trait(&self, type_name_map: &TypeNameMap) -> Option<clean::Type> {
        if self.trait_bounds.len() != 1 {
            return None;
        }
        // Safety: should never fails
        let trait_bound = self.trait_bounds.iter().nth(0).unwrap();
        if type_name(trait_bound, type_name_map, TypeNameLevel::All)
            == "core::convert::AsRef".to_string()
        {
            return extract_as_ref(trait_bound).and_then(|type_| {
                Some(clean::Type::BorrowedRef {
                    lifetime: None,
                    mutability: Mutability::Not,
                    type_: Box::new(type_),
                })
            });
        }
        return None;
    }

    pub fn _format_string_(&self, type_name_map: &TypeNameMap) -> String {
        let res = self
            .trait_bounds
            .iter()
            .map(|trait_bound| type_full_name(trait_bound, type_name_map, TypeNameLevel::All))
            .collect_vec();
        res.join(",")
    }

    pub fn can_be_replaced_with_type(
        &self,
        types: &HashMap<DefId, clean::Type>,
        type_name_map: &TypeNameMap,
        traits_of_type: &HashMap<DefId, HashSet<clean::Type>>,
    ) -> Option<clean::Type> {
        for (def_id, type_) in types {
            if let Some(traits) = traits_of_type.get(def_id) {
                let all_traits_satisified = self.trait_bounds.iter().all(|trait_bound| {
                    // We don't care about trait generics here
                    traits.iter().any(|trait_| {
                        type_full_name(trait_, type_name_map, TypeNameLevel::All)
                            == type_full_name(trait_bound, type_name_map, TypeNameLevel::All)
                    })
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
