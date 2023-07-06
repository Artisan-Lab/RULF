use crate::clean::{GenericArg, GenericArgs};
use crate::clean::{Path, Type};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_graph::{ApiGraph, TypeContext};
use crate::fuzz_target::api_util::{self, _type_name};
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::statistic;
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::{cell::RefCell, rc::Rc};

static EMPTY_IMPLS: Vec<(Path, GenericParamMap, DefId)> = Vec::new();

pub(crate) struct GenericSolver<'a> {
    generic_param: Vec<String>,
    current: Vec<usize>,
    current_function: &'a GenericFunction,
    all_visited: FxHashSet<DefId>, // set of impl id
    type_context: Rc<RefCell<TypeContext>>,
    type_trait_impls: &'a FxHashMap<DefId, Vec<(Path, GenericParamMap, DefId)>>,
    cache: &'a Cache,
    solutions: Vec<ApiFunction>,
}

/* #[derive(Clone)]
pub(crate) struct TypeContext<'a> {
    pub(crate) type_candidates: &'a Vec<Type>,
} */

impl<'a> GenericSolver<'a> {
    pub(crate) fn new(
        cache: &'a Cache,
        type_context: Rc<RefCell<TypeContext>>,
        type_trait_impls: &'a FxHashMap<DefId, Vec<(Path, GenericParamMap, DefId)>>,
        generic_function: &'a GenericFunction,
    ) -> GenericSolver<'a> {
        let len = generic_function.bounds_map.inner.len();
        let mut generic_param = Vec::new();
        for param in generic_function.bounds_map.inner.keys() {
            generic_param.push(param.to_string());
        }
        println!("[Solver] generic_param: {:?}", generic_param);
        GenericSolver {
            generic_param,
            type_context,
            type_trait_impls,
            current: Vec::new(),
            current_function: generic_function,
            all_visited: FxHashSet::<DefId>::default(),
            solutions: Vec::new(),
            cache,
        }
    }

    fn get_generic_param_type(&self, name: &str) -> Type {
        for i in 0..self.generic_param.len() {
            if self.generic_param[i] == name {
                return self.type_context.borrow().get_sorted_type()[self.current[i]].clone();
            }
        }
        unreachable!("cound not find name!");
    }

    fn make_function(&self) -> ApiFunction {
        let mut func = self.current_function.api_function.clone();
        func.mono = true;
        let mut replace_generic = |type_: &Type| -> Option<Type> {
            if let Type::Generic(sym) = type_ {
                Some(self.get_generic_param_type(sym.as_str()))
            } else {
                None
            }
        };
        for type_ in &mut func.inputs {
            *type_ = api_util::replace_type_with(type_, &mut replace_generic);
        }
        if let Some(ref output) = func.output {
            func.output = Some(api_util::replace_type_with(output, &mut replace_generic));
        }
        func
    }

    fn get_type_impls(&self, type_: &Type) -> &Vec<(Path, GenericParamMap, DefId)> {
        let did = type_.def_id(self.cache).expect(&format!("did fail: {type_:?}"));
        // TODO: identify variant, e.g. &mut T, T may have different trait impl. So do Vec<T>, Vec<i32>.

        if let Some(res) = self.type_trait_impls.get(&did) { res } else { &EMPTY_IMPLS }
    }

    pub(crate) fn is_trait_match_impl(
        &self,
        impl_trait: &Type,
        impl_generics: &GenericParamMap,
        trait_: &Type,
    ) -> bool {
        // replace generic function
        let generic_type = if let Type::Generic(sym) = *trait_ {
            Some(self.get_generic_param_type(sym.as_str()))
        } else {
            None
        };
        let mut trait_ = trait_;
        if generic_type.is_some() {
            trait_ = generic_type.as_ref().unwrap();
        }

        // println!("try to match {} and {}", _type_name(impl_trait), _type_name(trait_));
        match (impl_trait, trait_) {
            (Type::Generic(sym), _) => {
                return false; // FIXME: this is a sound approxiation
                let bounds = impl_generics.get_bounds(sym.as_str());
                let vec_traits = self.get_type_impls(trait_);
                println!(
                    "[Solver] Check if {} fit {} : {:?}",
                    _type_name(trait_),
                    sym.as_str(),
                    bounds
                );
                if let Some(_) = self.extract_type_impls_with_bounds(vec_traits, bounds) {
                    return true;
                }
                return false;
            }
            (Type::ImplTrait(_), _) | (_, Type::ImplTrait(_)) => {
                unimplemented!("ImplTrait should not occur");
            }
            (Type::Primitive(impl_ty), Type::Primitive(ty)) => {
                return *impl_ty == *ty;
            }
            (Type::Path { path: impl_trait }, Type::Path { path: trait_ }) => {
                if impl_trait.def_id() != trait_.def_id() {
                    // println!("unmatch: defid");
                    return false;
                }
                let impl_args = &impl_trait.segments.last().unwrap().args;
                let trait_args = &trait_.segments.last().unwrap().args;
                if matches!(impl_args, GenericArgs::Parenthesized { .. })
                    || matches!(impl_args, GenericArgs::Parenthesized { .. })
                {
                    println!(
                        "ignore unsupport parenthesized args:\n{:?}\n{:?}",
                        impl_trait, trait_
                    );
                    return false;
                }
                if let (
                    GenericArgs::AngleBracketed {
                        args: ref impl_args,
                        bindings: ref impl_bindings,
                    },
                    GenericArgs::AngleBracketed {
                        args: ref trait_args,
                        bindings: ref trait_bindings,
                    },
                ) = (impl_args, trait_args)
                {
                    //
                    for i in 0..impl_args.len() {
                        if let (GenericArg::Type(ref impl_arg), GenericArg::Type(ref trait_arg)) =
                            (&impl_args[i], &trait_args[i])
                        {
                            if !self.is_trait_match_impl(impl_arg, impl_generics, trait_arg) {
                                /* println!(
                                    "unmatch: {} {}",
                                    _type_name(impl_arg),
                                    _type_name(trait_arg)
                                ); */
                                return false;
                            }
                        } else {
                            println!(
                                "ignore unsupport generic Args (Const or Lifetime): {:?} {:?}",
                                impl_args[i], trait_args[i]
                            );
                        }
                    }

                    // FIXME: assoc item compare
                    /* let mut match_bindings = 0;
                    for a_binding in impl_bindings {
                        for b_binding in trait_bindings {
                            if api_util::is_binding_match(a_binding, b_binding) {
                                match_bindings += 1;
                            }
                        }
                    }
                    if match_bindings < impl_bindings.len() {
                        return false;
                    } */
                }
                return true;
            }
            (Type::Tuple(impl_trait), Type::Tuple(trait_)) => {
                if impl_trait.len() != trait_.len() {
                    return false;
                }
                for (impl_trait, trait_) in impl_trait.iter().zip(trait_.iter()) {
                    if (!self.is_trait_match_impl(impl_trait, impl_generics, trait_)) {
                        return false;
                    }
                }
                return true;
            }
            (Type::Slice(impl_trait), Type::Slice(trait_))
            | (Type::Array(impl_trait, ..), Type::Array(trait_, ..))
            | (Type::RawPointer(_, impl_trait), Type::RawPointer(_, trait_))
            | (
                Type::BorrowedRef { type_: impl_trait, .. },
                Type::BorrowedRef { type_: trait_, .. },
            ) => {
                return self.is_trait_match_impl(impl_trait, impl_generics, trait_);
            }
            _ => {
                //unimplemented!("unexpected type {:?} {:?}", impl_trait, trait_);
                return false;
            }
        }
    }

    /// return the exact impl_id set for type in given trait bounds
    /// if return None, it means this type do not satisfy bounds
    pub(crate) fn extract_type_impls_with_bounds(
        &self,
        impl_traits: &Vec<(Path, GenericParamMap, DefId)>, // trait, generic, impl_id
        bounds: &Vec<Path>,
    ) -> Option<FxHashSet<DefId>> {
        let mut res = FxHashSet::default();
        /* println!("all impl_trait: ");
        for (impl_trait, impl_generics, impl_id) in impl_traits{
            let impl_trait = Type::Path { path: impl_trait.clone() };
            println!("{}",_type_name(&impl_trait));
        } */
        for trait_ in bounds.iter() {
            // ignore Sized
            let trait_ = Type::Path { path: trait_.clone() };
            if _type_name(&trait_) == "Sized" {
                continue;
            }
            let mut flag = false;
            for (impl_trait, impl_generics, impl_id) in impl_traits {
                let impl_trait = Type::Path { path: impl_trait.clone() };
                // println!("compare {:?} {:?}",impl_trait,trait_);
                if self.is_trait_match_impl(&impl_trait, impl_generics, &trait_) {
                    res.insert(*impl_id);
                    flag = true;
                    //break;
                }
            }
            if !flag {
                return None;
            }
        }
        //println!("get!");
        Some(res)
    }

    /* fn get_current_type(&self, no: usize) -> &Type {
        &(self.type_context.borrow().get_sorted_type()[self.current[no]])
    } */

    // check if solution is valid
    fn check_pred(&mut self) -> bool {
        let union = |a: &mut FxHashSet<DefId>, b: &FxHashSet<DefId>| {
            for id in b {
                a.insert(*id);
            }
        };
        let mut visited = FxHashSet::<DefId>::default();
        for i in 0..self.current.len() {
            let param = &self.generic_param[i];
            let bounds = self.current_function.bounds_map.get_bounds(param);
            if bounds.is_empty() {
                continue;
            }
            let tuple = self
                .get_type_impls(&(self.type_context.borrow().get_sorted_type()[self.current[i]]));

            if let Some(impl_set) = self.extract_type_impls_with_bounds(tuple, bounds) {
                union(&mut visited, &impl_set);
            } else {
                return false;
            }
        }

        for (type_, bounds) in self.current_function.bounds_map.type_pred.iter() {
            let tuple = match (type_) {
                Type::Generic(sym) => {
                    self.get_type_impls(&self.get_generic_param_type(sym.as_str()))
                }
                Type::QPath(qpathdata) => {
                    // FIXME: currently we ignore assoc item
                    println!("[Solver] ignore QPath {:?}", type_);
                    continue;
                }
                _ => self.get_type_impls(type_),
            };

            if let Some(impl_set) = self.extract_type_impls_with_bounds(tuple, bounds) {
                union(&mut visited, &impl_set);
            } else {
                return false;
            }
        }

        print!("[Solver] valid combination: ");
        for i in 0..self.current.len() {
            let param = &self.generic_param[i];
            print!(
                "{}: {}, ",
                param,
                _type_name(&(self.type_context.borrow().get_sorted_type()[self.current[i]]))
            );
        }
        print!("visited {:?}, all_visited {:?}", visited, self.all_visited);
        print!("\n");
        if visited.is_subset(&self.all_visited) {
            return false;
        }
        print!("[Solver] this combination is selected\n");
        union(&mut self.all_visited, &visited);
        true
    }

    fn search(&mut self, param_no: usize) {
        let len = self.type_context.borrow().get_sorted_type().len();
        if param_no >= self.generic_param.len() {
            if self.check_pred() {
                let func = self.make_function();
                println!("find solutions: {}", func._pretty_print());
                self.solutions.push(func);
            }
            return;
        }

        // dfs searching
        for i in 0..len {
            self.current[param_no] = i;
            self.search(param_no + 1);
        }
    }

    fn print_all_candidates(&self) {
        println!("=======Type=======");
        for type_ in self.type_context.borrow().get_sorted_type().iter() {
            println!("{}", _type_name(type_));
        }
        println!("==================");
    }

    pub(crate) fn solve(&mut self) {
        println!("[Solver] find solution for {}", self.current_function.api_function.full_name);
        let len = self.generic_param.len();
        self.current.resize(len, 0);
        //self.print_all_candidates();
        self.search(0);
    }

    pub(crate) fn take_solutions(&mut self) -> Vec<ApiFunction> {
        let mut res = Vec::new();
        while let Some(func) = self.solutions.pop() {
            res.push(func);
        }
        res
    }
}
