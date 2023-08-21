use crate::clean::types::{GenericArgs, Path, Type};
use crate::clean::{self, GenericBound, Generics, PolyTrait, WherePredicate};
use crate::clean::{GenericParamDefKind, Trait};
use crate::formats::cache::Cache;
use crate::fuzz_target::{api_function::ApiFunction, api_util, impl_util::FullNameMap};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::collections::hash_map::Iter;
use std::f32::consts::E;
use std::ops::{Deref, DerefMut};

#[derive(Debug, Clone)]
pub(crate) struct GenericParamMap {
    pub inner: FxHashMap<String, Vec<Path>>, // generic param => bounds(a set of trait path)
    pub type_pred: Vec<(Type, Vec<Path>)>,
}

fn is_solvable_bound(bound: &Path) -> bool {
    for segment in &bound.segments {
        if let GenericArgs::Parenthesized { .. } = segment.args {
            return false;
        }
    }
    return true;
}

impl GenericParamMap {
    pub fn iter(&self) -> Iter<'_, String, Vec<Path>> {
        self.inner.iter()
    }

    pub fn is_solvable(&self) -> bool {
        for (name, bounds) in self.inner.iter() {
            for bound in bounds {
                if !is_solvable_bound(bound) {
                    return false;
                }
            }
        }

        for (type_, bounds) in self.type_pred.iter() {
            for bound in bounds {
                if !is_solvable_bound(bound) {
                    return false;
                }
            }
        }
        return true;
    }

    pub fn new() -> GenericParamMap {
        GenericParamMap { inner: FxHashMap::<String, Vec<Path>>::default(), type_pred: Vec::new() }
    }

    pub fn get_bounds(&self, name: &str) -> &Vec<Path> {
        self.inner.get(name).unwrap()
    }

    pub fn add_generics(&mut self, generics: &Generics) {
        for param in generics.params.iter() {
            match &param.kind {
                GenericParamDefKind::Type { did, bounds, .. } => {
                    self.add_generic_bounds(param.name.as_str(), &bounds);
                }
                GenericParamDefKind::Const { .. } => {
                    println!("ignore const: {:?}", param);
                }
                GenericParamDefKind::Lifetime { .. } => {
                    // println!("ignore lifetime: {:?}", param);
                }
            }
        }
        for param in generics.where_predicates.iter() {
            match param {
                WherePredicate::BoundPredicate { ty, bounds, bound_params } => {
                    self.type_pred.push((ty.clone(), self.bounds_to_vec(bounds)));
                }
                WherePredicate::RegionPredicate { lifetime, bounds } => {
                    println!("ignore RegionPredicate: {:?}", param);
                }
                WherePredicate::EqPredicate { lhs, rhs, bound_params } => {
                    println!("ignore EqPredicate: {:?}", param);
                }
            }
        }
    }

    fn bounds_to_vec(&self, bounds: &[GenericBound]) -> Vec<Path> {
        let mut res = Vec::new();
        for bound in bounds {
            match bound {
                GenericBound::TraitBound(poly, _) => {
                    res.push(poly.trait_.clone());
                    // traitbound should not include type generic information, we must assure this
                    for param in &poly.generic_params {
                        if param.is_type() {
                            unreachable!("type generic params inside traitbound!");
                        }
                    }
                }
                GenericBound::Outlives(lifetime) => {
                    println!("bounds to facts ignore lifetime: {:?}", lifetime);
                }
            }
        }
        res
    }

    pub fn add_generic_bounds(&mut self, name: &str, bounds: &[GenericBound]) {
        let v = self.bounds_to_vec(bounds);
        if let Some(bounds) = self.inner.get_mut(name) {
            for p in v {
                bounds.push(p);
            }
        } else {
            self.inner.insert(name.to_string(), v);
        }
    }
}

impl Deref for GenericParamMap {
    type Target = FxHashMap<String, Vec<Path>>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
