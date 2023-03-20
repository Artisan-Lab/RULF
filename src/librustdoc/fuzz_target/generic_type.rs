use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_hir::Mutability;
use std::{
    collections::{HashMap, HashSet},
    convert::TryFrom,
};

use crate::clean::{self, GenericBound};

use super::type_name::{type_full_name, type_name, TypeNameLevel, TypeNameMap};
use super::type_util::{extract_only_one_type_parameter, mutable_u8_slice_type};
use super::type_util::{i32_type, str_type, u8_slice_type};

// FIXME: Why these are not marker from std?.
pub static NUMERIC_TRAITS: [&'static str; 11] = [
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
    "serde::ser::Serialize", // for serde_json
];
pub static U8_SLICE_TRAITS: [&'static str; 3] = [
    "std::io::Read",
    "std::io::BufRead",
    "regex::bytes::Replacer", // for regex
];
pub static MUT_U8_SLICE_TRAITS: [&'static str; 1] = ["std::io::Write"];
pub static STR_SLICE_TRAITS: [&'static str; 5] = [
    "core::convert::AsRef<Str>",
    "core::convert::Into<String>",
    "core::convert::Into<std::ffi::os_str::OsString>",
    "core::clone::Clone",
    "regex::Replacer", // for regex
];

#[derive(Debug, Clone, Copy)]
pub enum GenericBoundError {
    Lifetime,
    Sized,
}

/// This represents generic bound without `trait with generic`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimplifiedGenericBound {
    trait_bounds: HashSet<clean::Type>,
}

pub enum ReplaceType {
    Numeric,
    U8Slice,
    MutU8Slice,
    Str,
    RefTrait(clean::Type),
    IntoTrait(clean::Type),
    DefinedType(clean::Type),
}

impl ReplaceType {
    pub fn to_replace_type(&self) -> clean::Type {
        match self {
            ReplaceType::Numeric => i32_type(),
            ReplaceType::U8Slice => u8_slice_type(),
            ReplaceType::MutU8Slice => mutable_u8_slice_type(),
            ReplaceType::Str => str_type(),
            ReplaceType::DefinedType(ty_)
            | ReplaceType::RefTrait(ty_)
            | ReplaceType::IntoTrait(ty_) => ty_.to_owned(),
        }
    }

    pub fn is_primitive_type(&self) -> bool {
        match self {
            ReplaceType::Numeric
            | ReplaceType::Str
            | ReplaceType::U8Slice
            | ReplaceType::MutU8Slice => true,
            _ => false,
        }
    }

    pub fn is_convert_trait(&self) -> bool {
        match self {
            ReplaceType::RefTrait(..) | ReplaceType::IntoTrait(..) => true,
            _ => false,
        }
    }

    pub fn is_defined_type(&self) -> bool {
        match self {
            ReplaceType::DefinedType(..) => true,
            _ => false,
        }
    }

    pub fn _print_replace_massage(&self, generic: &str, type_name_map: &TypeNameMap) {
        match self {
            ReplaceType::Numeric => info!("{} can be replaced with numeric", generic),
            ReplaceType::U8Slice => info!("{} can be replaced with &[u8]", generic),
            ReplaceType::MutU8Slice => info!("{} can be replaced with &mut [u8]", generic),
            ReplaceType::Str => info!("{} can be replaced with str", generic),
            ReplaceType::DefinedType(type_)
            | ReplaceType::RefTrait(type_)
            | ReplaceType::IntoTrait(type_) => {
                let type_full_name = type_full_name(type_, type_name_map, TypeNameLevel::All);
                info!("{} can be replaced with {}", generic, type_full_name);
            }
        }
    }
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

    pub fn is_empty(&self) -> bool {
        self.trait_bounds.is_empty()
    }

    pub fn default_type_for_empty_bounds() -> clean::Type {
        i32_type()
    }

    /// determine whether a generic bound can be replaced with some type
    pub fn can_be_some_type(
        &self,
        types: &HashMap<DefId, clean::Type>,
        type_name_map: &TypeNameMap,
        traits_of_type: &HashMap<DefId, HashSet<clean::Type>>,
    ) -> Option<ReplaceType> {
        if self.can_be_numeric_type(type_name_map) {
            Some(ReplaceType::Numeric)
        } else if self.can_be_u8_slice(type_name_map) {
            Some(ReplaceType::U8Slice)
        } else if self.can_be_mut_u8_slice(type_name_map) {
            Some(ReplaceType::MutU8Slice)
        } else if self.can_be_str_slice(type_name_map) {
            Some(ReplaceType::Str)
        } else if let Some(ref_type) = self.is_as_ref_trait(type_name_map) {
            Some(ReplaceType::RefTrait(ref_type))
        } else if let Some(into_type) = self.is_into_trait(type_name_map) {
            Some(ReplaceType::IntoTrait(into_type))
        } else if let Some(defined_type) =
            self.can_be_defined_type(types, type_name_map, traits_of_type)
        {
            Some(ReplaceType::DefinedType(defined_type))
        } else {
            None
        }
    }

    // determine whether a bound can be a primitive type
    pub fn can_be_numeric_type(&self, type_name_map: &TypeNameMap) -> bool {
        // FIXME: This is a very naive implementation. We only compare if trait names are equal.
        self.trait_bounds.iter().all(|trait_bound| {
            let trait_name = type_full_name(trait_bound, type_name_map, TypeNameLevel::All);
            NUMERIC_TRAITS.iter().any(|primitive_trait| *primitive_trait == &trait_name)
        })
    }

    pub fn can_be_u8_slice(&self, type_name_map: &TypeNameMap) -> bool {
        self.trait_bounds.iter().all(|trait_bound| {
            let trait_name = type_full_name(trait_bound, type_name_map, TypeNameLevel::All);
            U8_SLICE_TRAITS.iter().any(|primitive_trait| *primitive_trait == &trait_name)
        })
    }

    pub fn can_be_mut_u8_slice(&self, type_name_map: &TypeNameMap) -> bool {
        self.trait_bounds.iter().all(|trait_bound| {
            let trait_name = type_full_name(trait_bound, type_name_map, TypeNameLevel::All);
            MUT_U8_SLICE_TRAITS.iter().any(|primitive_trait| *primitive_trait == &trait_name)
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
            return extract_only_one_type_parameter(trait_bound).and_then(|type_| {
                Some(clean::Type::BorrowedRef {
                    lifetime: None,
                    mutability: Mutability::Not,
                    type_: Box::new(type_),
                })
            });
        }
        return None;
    }

    pub fn is_into_trait(&self, type_name_map: &TypeNameMap) -> Option<clean::Type> {
        if self.trait_bounds.len() != 1 {
            return None;
        }
        // Safety: should never fails
        let trait_bound = self.trait_bounds.iter().nth(0).unwrap();
        if type_name(trait_bound, type_name_map, TypeNameLevel::All)
            == "core::convert::Into".to_string()
        {
            return extract_only_one_type_parameter(trait_bound);
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

    pub fn can_be_defined_type(
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
