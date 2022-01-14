use std::collections::HashSet;

use crate::clean::{self, GenericBound};

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

    // // determine whether a bound can be a primitive type
    // pub fn can_be_primitive_type(&self) -> bool {
    //     // FIXME: This is a very naive implementation. We only compare if trait names are equal.
    //     // This is because we may not 
    // }
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
