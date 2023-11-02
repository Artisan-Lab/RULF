use crate::clean::types::QPathData;
use crate::clean::Path;
use crate::clean::PrimitiveType;
use crate::clean::Term;
use crate::clean::Type;
use crate::clean::TypeBindingKind;
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
use crate::fuzz_target::generic_solution::match_type;
use crate::fuzz_target::generic_solution::merge_solution_set;
use crate::fuzz_target::generic_solution::{merge_solution, solution_string};
use crate::fuzz_target::generic_solver::GenericSolver;
use crate::fuzz_target::impl_id::ImplId;
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
use rustc_hir::{self, Mutability};
use std::cmp::{max, min};
use std::{cell::RefCell, rc::Rc};

use super::api_util::print_path_segment;

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

    fn check_assoc_item_type(&self, name: &str, type_: &Type) -> bool {
        for assoc_item in self.assoc_items.iter() {
            if print_path_segment(&assoc_item.0.assoc) == name {
                if let Some(_) = match_type(&assoc_item.1, type_, &Vec::new()) {
                    return true;
                } else {
                    return false;
                }
            }
        }
        unreachable!("unknown assoc item name: {}", name);
    }

    pub fn check_assoc_items(&self, trait_: &Path) -> bool {
        if let Some(bindings) = trait_.bindings() {
            for binding in bindings.iter() {
                let name = print_path_segment(&binding.assoc);
                match binding.kind {
                    TypeBindingKind::Equality { ref term } => {
                        if let Term::Type(assoc_ty) = term {
                            if !self.check_assoc_item_type(&name, assoc_ty) {
                                return false;
                            }
                        }
                    }
                    _ => {
                        unreachable!("generic bounds in binding: {:?}", binding);
                    }
                }
            }
        }
        return true;
    }
}

static EMPTY_IMPLS: Vec<TraitImpl> = Vec::new();

pub(crate) struct TraitImplMap {
    pub(crate) inner: FxHashMap<DefId, Vec<TraitImpl>>,
}

/*
    Iterator<Item>
    T::sss :
*/

fn is_impl_in_std(type_: &Type, trait_: &Type, cache: &Cache) -> bool {
    match _type_name(trait_, Some(cache)).as_str() {
        "std::alloc::Allocator" => {
            match _type_name(type_, Some(cache)).as_str() {
                "std::alloc::Global" => return true,
                _ => {}
            }
            false
        }
        "std::hash::Hash" => {
            // Hash is implemented for [T], String, ix, ux
            match _type_name(type_, Some(cache)).as_str() {
                "std::string::String" => return true,
                _ => {}
            }
            match type_ {
                Type::Slice(ref inner) => {
                    return is_impl_in_std(inner, trait_, cache);
                }
                Type::Primitive(primitive) => match primitive {
                    PrimitiveType::I8
                    | PrimitiveType::I16
                    | PrimitiveType::I32
                    | PrimitiveType::I64
                    | PrimitiveType::I128
                    | PrimitiveType::U8
                    | PrimitiveType::U16
                    | PrimitiveType::U32
                    | PrimitiveType::U64
                    | PrimitiveType::U128
                    | PrimitiveType::Str => return true,
                    _ => {}
                },
                _ => {}
            }
            false
        }
        "std::io::Write" => {
            println!("[Weapon] Detect io::Write");
            match _type_name(type_, Some(cache)).as_str() {
                "&mut [u8]" => return true,
                "std::vec::Vec::<u8, std::alloc::Global>" => return true,
                _ => {}
            };
            match type_ {
                Type::BorrowedRef { lifetime, mutability, type_ } => {
                    if matches!(mutability, Mutability::Mut) {
                        //impl<W: Write + ?Sized> Write for &mut W
                        return is_impl_in_std(type_, trait_, cache); // TODO: replace with extract_trait_id for better precision.
                    }
                }
                _ => {}
            }
            false
        }
        "std::io::Read" => {
            println!("[Weapon] Detect io::Read");
            match _type_name(type_, Some(cache)).as_str() {
                "&[u8]" | "&mut [u8]" => return true,
                _ => {}
            }
            match type_ {
                Type::BorrowedRef { lifetime, mutability, type_ } => {
                    if matches!(mutability, Mutability::Mut) {
                        //impl<R: Read + ?Sized> Read for &mut R
                        return is_impl_in_std(type_, trait_, cache);
                    }
                }
                _ => {}
            }
            false
        }
        "core::marker::Sized" => true,
        _ => false,
    }
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
    ) -> Option<FxHashSet<ImplId>> {
        let mut res = FxHashSet::default();
        let trait_impls = self.get_type_impls(type_, cache); //trait, generic, impl_id

        // check whether type_ have trait_
        let mut extract_trait_id = |trait_: &Type| -> Option<ImplId> {
            for trait_impl in trait_impls {
                let impl_trait = Type::Path { path: trait_impl.trait_.clone() };
                // TODO: should we consider blanket impl?
                /* if trait_impl.generic_map.generic_defs.len() > 0 {
                    // ignore blanket impl
                    continue;
                } */
                if let Some(sol_for_trait) =
                    match_type(&trait_, &impl_trait, &trait_impl.generic_map.generic_defs)
                {
                    // check trait_ associate item
                    // TODO: Add Associate item check
                    /* match trait_ {
                        Type::Path { ref path } => {
                            if !trait_impl.check_assoc_items(path) {
                                continue;
                            }
                        }
                        _ => unreachable!(),
                    }; */

                    let for_type = if let Some(ref type_) = trait_impl.blanket_type {
                        type_.clone()
                    } else {
                        trait_impl.for_.clone()
                    };
                    if let Some(sol_for_type) =
                        match_type(type_, &for_type, &trait_impl.generic_map.generic_defs)
                    {
                        println!(
                            "[TraitImpl] {} match {}, {} match {}",
                            _type_name(&trait_, None),
                            _type_name(&impl_trait, None),
                            _type_name(type_, None),
                            _type_name(&trait_impl.for_, None)
                        );

                        if let Some(solution) = merge_solution(
                            &sol_for_type,
                            &sol_for_trait,
                            &trait_impl.generic_map.generic_defs,
                        ) {
                            println!(
                                "[TraitImpl] Recursively check: do we have impl {} for {}?",
                                _type_name(&impl_trait, Some(cache)),
                                _type_name(&for_type, Some(cache))
                            );
                            println!(
                                "[TraitImpl] solution: {}, generic_defs: {:?}",
                                solution_string(&solution),
                                trait_impl.generic_map.generic_defs
                            );

                            if solution.is_empty()
                                || trait_impl
                                    .generic_map
                                    .check_solution(&solution, trait_impl_map, cache)
                                    .is_some()
                            {
                                return Some(ImplId::Id(trait_impl.impl_id));
                            }
                        }
                    }
                }
            }
            None
        };

        for trait_ in bounds.iter() {
            let trait_ = Type::Path { path: trait_.clone() };

            if is_impl_in_std(&type_, &trait_, cache) {
                //TODO: Merge into extract_trait_id for better acc
                res.insert(ImplId::Unknown);
                continue;
            }

            if let Some(impl_id) = extract_trait_id(&trait_) {
                res.insert(impl_id);
                continue;
            }

            println!(
                "[TraitImpl] Check trait {} for {} fail",
                _type_name(&trait_, Some(cache)),
                _type_name(&type_, Some(cache))
            );
            return None;
        }

        Some(res)
    }
}
