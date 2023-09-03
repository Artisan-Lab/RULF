use crate::clean::types::QPathData;
use crate::clean::Path;
use crate::clean::PrimitiveType;
use crate::clean::Type;
use crate::clean::Visibility;
use crate::clean::{GenericArg, GenericArgs};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_sequence::{ApiCall, ApiSequence, ParamType};
use crate::fuzz_target::api_util::_type_name;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzz_target_renderer::FuzzTargetContext;
use crate::fuzz_target::fuzzable_type;
use crate::fuzz_target::fuzzable_type::FuzzableType;
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::generic_solution::{merge_solution, solution_string};
use crate::fuzz_target::generic_solver::GenericSolver;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::mod_visibility::ModVisibity;
use crate::fuzz_target::prelude_type;
use crate::fuzz_target::statistic;
use crate::html::format::join_with_double_colon;
use crate::TyCtxt;
use lazy_static::lazy_static;
use rand::{self, Rng};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::cmp::{max, min};
use std::{cell::RefCell, rc::Rc};

use super::generic_solution::match_type;
use super::generic_solution::merge_solution_set;
pub(crate) struct TraitImpl {
    pub(crate) trait_: Path,
    pub(crate) for_: Type,
    pub(crate) blanket_type: Option<Type>,
    pub(crate) generic_map: GenericParamMap,
    pub(crate) impl_id: DefId,
    pub(crate) assoc_items: Vec<(QPathData, Type)>,
}

impl TraitImpl {
    pub(crate) fn new(
        trait_: Path,
        for_: Type,
        blanket_type: Option<Type>,
        generic_map: GenericParamMap,
        impl_id: DefId,
    ) -> TraitImpl {
        TraitImpl { trait_, for_, impl_id, blanket_type, generic_map, assoc_items: Vec::new() }
    }
}

static EMPTY_IMPLS: Vec<TraitImpl> = Vec::new();

pub(crate) struct TraitImplMap {
    pub(crate) inner: FxHashMap<DefId, Vec<TraitImpl>>,
}

impl TraitImplMap {
    pub(crate) fn new() -> TraitImplMap {
        TraitImplMap { inner: FxHashMap::default() }
    }
    pub(crate) fn add_type_trait_impl(&mut self, ty_did: DefId, trait_impl: TraitImpl) {
        self.inner.entry(ty_did).or_default().push(trait_impl);
    }

    fn get_type_impls(&self, type_: &Type, cache: &Cache) -> &Vec<TraitImpl> {
        let did = type_.def_id(cache).expect(&format!("did fail: {type_:?}"));
        // TODO: identify variant, e.g. &mut T, T may have different trait impl. So do Vec<T>, Vec<i32>.
        if let Some(res) = self.inner.get(&did) { res } else { &EMPTY_IMPLS }
    }

    /// return the exact impl_id set for type in given trait bounds
    /// if return None, it means this type do not satisfy bounds
    pub(crate) fn extract_type_impls_with_bounds(
        &self,
        type_: &Type,
        bounds: &Vec<Path>,
        cache: &Cache,
        trait_impl_map: &TraitImplMap,
    ) -> Option<FxHashSet<DefId>> {
        let mut res = FxHashSet::default();
        let trait_impls = self.get_type_impls(type_, cache); //trait, generic, impl_id

        for trait_ in bounds.iter() {
            let trait_ = Type::Path { path: trait_.clone() };
            if _type_name(&trait_, None) == "Sized" {
                continue;
            }
            let mut success = false;
            for trait_impl in trait_impls {
                let impl_trait = Type::Path { path: trait_impl.trait_.clone() };
                /* if trait_impl.generic_map.generic_defs.len()>0{
                    continue;
                } */
                if let Some(sol_for_trait) =
                    match_type(&trait_, &impl_trait, &trait_impl.generic_map.generic_defs)
                {
                    let for_type = if let Some(ref type_) = trait_impl.blanket_type {
                        type_.clone()
                    } else {
                        trait_impl.for_.clone()
                    };
                    if let Some(sol_for_type) =
                        match_type(type_, &for_type, &trait_impl.generic_map.generic_defs)
                    {
                        // FIXME: add type pred checking

                        println!(
                            "[TraitImpl] {} match {}, {} match {}",
                            _type_name(&trait_, None),
                            _type_name(&impl_trait, None),
                            _type_name(type_, None),
                            _type_name(&trait_impl.for_, None)
                        );
                        println!(
                            "sol for trait: {}, sol for type: {}, generic_defs: {:?}",
                            solution_string(&sol_for_trait),
                            solution_string(&sol_for_type),
                            trait_impl.generic_map.generic_defs
                        );
                        if let Some(solution) = merge_solution(
                            &sol_for_type,
                            &sol_for_trait,
                            &trait_impl.generic_map.generic_defs,
                        ) {
                            println!(
                                "[TraitImpl] Recursively check solution: {}",
                                solution_string(&solution)
                            );
                            if solution.is_empty()
                                || trait_impl.generic_map.check_solution(
                                    &solution,
                                    trait_impl_map,
                                    cache,
                                )
                            {
                                res.insert(trait_impl.impl_id);
                                success = true;
                                break;
                            }
                        }
                    }
                }
            }
            if !success {
                println!("[TraitImpl] Check trait {} fail", _type_name(&trait_, None));
                return None;
            }
        }

        /* for trait_ in bounds.iter() {

            // workaround to ignore Sized, assuming all candidates are not DST.
            if _type_name(&trait_, None) == "Sized" {
                continue;
            }

            if let Some(impl_id) = extract_trait_id(type_, &trait_) {
                res.insert(impl_id);
            } else {
                println!("[TraitImpl] Check trait {} fail", _type_name(&trait_, None));
                return None;
            }
        } */
        //println!("get!");
        Some(res)
    }
}
