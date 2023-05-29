use crate::clean::Type::Generic;
use crate::clean::{self, GenericBound, WherePredicate};
use crate::clean::{GenericParamDefKind, Trait};
use crate::formats::cache::Cache;
use crate::fuzz_target::{api_function::ApiFunction, api_util, impl_util::FullNameMap};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::collections::hash_set::Iter;
use std::ops::{Deref, DerefMut};

#[derive(PartialEq, Default, Clone, Debug)]
pub(crate) struct DefSet {
    defs: FxHashSet<DefId>,
}

impl DefSet {
    pub fn new() -> DefSet {
        DefSet { defs: FxHashSet::default() }
    }
    pub fn union(&mut self,other:&DefSet) {
        for el in other.iter(){
            self.insert(*el);
        }
    }
    /*     pub fn insert(&mut self, did: DefId) {
        self.traits.insert(did);
    }
    pub fn iter(&self) -> Iter<'_, DefId> {
        self.traits.iter()
    } */
}

impl Deref for DefSet {
    type Target = FxHashSet<DefId>;
    fn deref(&self) -> &Self::Target {
        &self.defs
    }
}

impl DerefMut for DefSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.defs
    }
}

impl PartialOrd for DefSet {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let sub1 = self.defs.is_subset(&other.defs);
        let sub2 = other.defs.is_subset(&self.defs);
        match (sub1, sub2) {
            (true, true) => Some(std::cmp::Ordering::Equal),
            (true, false) => Some(std::cmp::Ordering::Less),
            (false, true) => Some(std::cmp::Ordering::Greater),
            (false, false) => None,
        }
    }
}
/* 
impl Default for DefSet {
    fn default() -> Self {
        Self { defs: Default::default() }
    }
}
 */