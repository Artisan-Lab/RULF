use crate::clean::{GenericArg, GenericArgs};
use crate::clean::{Path, Type};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_graph::{ApiGraph, TypeContext};
use crate::fuzz_target::api_util::{self, _type_name};
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::statistic;
use crate::fuzz_target::trait_impl::TraitImpl;
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::cmp::Eq;
use std::hash::Hash;
use std::time::Instant;
use std::{cell::RefCell, rc::Rc};

static EMPTY_IMPLS: Vec<TraitImpl> = Vec::new();
static MAX_MONO_PER_FUNC: usize = 3;
fn set_union<T: Eq + Hash + Copy>(a: &mut FxHashSet<T>, b: &FxHashSet<T>) {
    for id in b {
        a.insert(*id);
    }
}

pub(crate) struct GenericSolver<'a> {
    generic_param: Vec<String>,
    current: Vec<usize>,
    current_function: &'a GenericFunction,
    all_visited: FxHashSet<DefId>, // set of impl id
    all_callable: FxHashSet<(i32, i32)>,
    type_context: Rc<RefCell<TypeContext>>,
    type_trait_impls: &'a FxHashMap<DefId, Vec<TraitImpl>>,
    cache: &'a Cache,
    full_name_map: &'a FullNameMap,
    solutions: Vec<ApiFunction>,
    solution_count: usize,
    solvable: bool,
    try_count:usize,
}


impl<'a> GenericSolver<'a> {
    pub(crate) fn new(
        cache: &'a Cache,
        full_name_map: &'a FullNameMap,
        type_context: Rc<RefCell<TypeContext>>,
        type_trait_impls: &'a FxHashMap<DefId, Vec<TraitImpl>>,
        generic_function: &'a GenericFunction,
    ) -> GenericSolver<'a> {
        let len = generic_function.bounded_symbols.len();
        let mut generic_param = Vec::new();
        let solvable = generic_function.generic_map.is_solvable();
        for param in generic_function.bounded_symbols.iter() {
            generic_param.push(param.to_string());
        }
        // println!("[Solver] generic_param: {:?}", generic_param);
        GenericSolver {
            all_callable: FxHashSet::<(i32, i32)>::default(),
            generic_param,
            type_context,
            type_trait_impls,
            current: Vec::new(),
            current_function: generic_function,
            all_visited: FxHashSet::<DefId>::default(),
            solutions: Vec::new(),
            cache,
            full_name_map,
            solvable,
            solution_count: 0,
            try_count:0
        }
    }

    fn get_generic_param_type(&self, name: &str) -> Option<Type> {
        for i in 0..self.generic_param.len() {
            if self.generic_param[i] == name {
                return Some(self.type_context.borrow().get_sorted_type()[self.current[i]].clone());
            }
        }
        if self.current_function.generic_map.inner.get(name).is_some() {
            return None;
        }
        unreachable!("cound not find name {}. params: {:?}", name, self.generic_param);
    }

    fn replace_generic(&self, type_: &Type) -> Type {
        let mut replace = |type_: &Type| -> Option<Type> {
            if let Type::Generic(sym) = type_ {
                self.get_generic_param_type(sym.as_str())
            } else {
                None
            }
        };
        api_util::replace_type_with(type_, &mut replace)
    }

    fn make_function(&self) -> ApiFunction {
        let mut func = self.current_function.api_function.clone();
        func.mono = true;

        for type_ in &mut func.inputs {
            *type_ = self.replace_generic(type_);
        }
        if let Some(ref output) = func.output {
            func.output = Some(self.replace_generic(output));
        }
        func
    }

    fn get_type_impls(&self, type_: &Type) -> &Vec<TraitImpl> {
        let did = type_.def_id(self.cache).expect(&format!("did fail: {type_:?}"));
        // TODO: identify variant, e.g. &mut T, T may have different trait impl. So do Vec<T>, Vec<i32>.
        if let Some(res) = self.type_trait_impls.get(&did) { res } else { &EMPTY_IMPLS }
    }

    pub(crate) fn is_trait_match_impl(
        &self,
        impl_type: &Type,
        trait_impl: &TraitImpl,
        trait_: &Type,
    ) -> bool {
        // replace generic function
        let generic_type = if let Type::Generic(sym) = *trait_ {
            self.get_generic_param_type(sym.as_str())
        } else {
            None
        };
        let mut trait_ = trait_;
        if generic_type.is_some() {
            trait_ = generic_type.as_ref().unwrap();
        }

        // println!("try to match {} and {}", _type_name(impl_trait), _type_name(trait_));
        match (impl_type, trait_) {
            (_, Type::Generic(_)) => {
                unreachable!("trait generic should be resolved: {:?}", trait_);
            }
            (Type::Generic(sym), _) => {
                return false; // FIXME: this is a sound approxiation
                let bounds = trait_impl.generic_map.get_bounds(sym.as_str());
                let vec_traits = self.get_type_impls(trait_);
                println!(
                    "[Solver] Check if {} fit {} : {:?}",
                    _type_name(trait_, Some(self.cache)),
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
                match (impl_args, trait_args) {
                    (
                        GenericArgs::AngleBracketed {
                            args: ref impl_args,
                            bindings: ref impl_bindings,
                        },
                        GenericArgs::AngleBracketed {
                            args: ref trait_args,
                            bindings: ref trait_bindings,
                        },
                    ) => {
                        // println!("[Solver] {} len = {} {} ",impl_args.len()!=trait_args.len(),impl_args.len(), trait_args.len());
                        // assert!(impl_args.len()==trait_args.len(), "{impl_args:?} {trait_args:?} should have same length");
                        let mut impl_iter = impl_args.iter();
                        let mut trait_iter = trait_args.iter();
                        while let (Some(impl_arg), Some(trait_arg)) =
                            (impl_iter.next(), trait_iter.next())
                        {
                            if let (
                                GenericArg::Type(ref impl_arg),
                                GenericArg::Type(ref trait_arg),
                            ) = (&impl_arg, &trait_arg)
                            {
                                if !self.is_trait_match_impl(impl_arg, trait_impl, trait_arg) {
                                    /* println!(
                                        "unmatch: {} {}",
                                        _type_name(impl_arg),
                                        _type_name(trait_arg)
                                    ); */
                                    return false;
                                }
                            } else {
                                /* println!(
                                    "ignore unsupport generic Args (Const or Lifetime): {:?} {:?}",
                                    impl_args[i], trait_args[i]
                                ); */
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
                    }
                    (_, _) => {
                        println!(
                            "ignore unsupport parenthesized args:\n{:?}\n{:?}",
                            impl_trait, trait_
                        );
                        return false;
                    }
                }
                // println!("match");
                return true;
            }
            (Type::Tuple(impl_trait), Type::Tuple(trait_)) => {
                if impl_trait.len() != trait_.len() {
                    return false;
                }
                for (impl_trait, trait_) in impl_trait.iter().zip(trait_.iter()) {
                    if (!self.is_trait_match_impl(impl_trait, trait_impl, trait_)) {
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
                return self.is_trait_match_impl(impl_trait, trait_impl, trait_);
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
        trait_impls: &Vec<TraitImpl>, // trait, generic, impl_id
        bounds: &Vec<Path>,
    ) -> Option<FxHashSet<DefId>> {
        let mut res = FxHashSet::default();

        for trait_ in bounds.iter() {
            let trait_ = Type::Path { path: trait_.clone() };
            // workaround to ignore Sized, assuming all candidates are not DST.
            if _type_name(&trait_, None) == "Sized" {
                continue;
            }
            let mut flag = false;
            for trait_impl in trait_impls {
                let impl_trait = Type::Path { path: trait_impl.trait_.clone() };
                // println!("compare {:?} {:?}",impl_trait,trait_);
                if self.is_trait_match_impl(&impl_trait, trait_impl, &trait_) {
                    res.insert(trait_impl.impl_id);
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

    fn is_current_callable(&self) -> bool {
        for type_ in self.current_function.api_function.inputs.iter() {
            let ty = self.replace_generic(type_);
            if !self.type_context.borrow().is_callable(&ty, self.full_name_map, self.cache) {
                return false;
            }
        }
        return true;
    }

    fn get_current_callable_type(&mut self) -> FxHashSet<(i32, i32)> {
        let mut callable = FxHashSet::<(i32, i32)>::default();
        for type_ in self.current_function.api_function.inputs.iter() {
            let ty = self.replace_generic(type_);
            let type_callable =
                self.type_context.borrow().get_callable(&ty, true, self.full_name_map, self.cache);
            set_union(&mut callable, &type_callable);
        }
        if let Some(ref output) = self.current_function.api_function.output {
            let ty = self.replace_generic(output);
            let type_callable =
                self.type_context.borrow().get_callable(&ty, false, self.full_name_map, self.cache);
            set_union(&mut callable, &type_callable);
        };
        callable
    }

    fn display_combination(&self) -> String {
        let mut res = String::new();
        for i in 0..self.current.len() {
            let param = &self.generic_param[i];
            res.push_str(&format!(
                "{}: {}, ",
                param,
                _type_name(
                    &(self.type_context.borrow().get_sorted_type()[self.current[i]]),
                    Some(self.cache)
                )
            ));
        }
        res
    }

    // check if solution is valid
    fn check_pred(&mut self) -> bool {
        let mut visited = FxHashSet::<DefId>::default();
        for i in 0..self.current.len() {
            let param = &self.generic_param[i];
            let bounds = self.current_function.generic_map.get_bounds(param);
            if bounds.is_empty() {
                continue;
            }
            let tuple = self
                .get_type_impls(&(self.type_context.borrow().get_sorted_type()[self.current[i]]));

            if let Some(impl_set) = self.extract_type_impls_with_bounds(tuple, bounds) {
                set_union(&mut visited, &impl_set);
            } else {
                return false;
            }
        }

        for (type_, bounds) in self.current_function.generic_map.type_pred.iter() {
            let tuple = match (type_) {
                Type::Generic(sym) => {
                    self.get_type_impls(&self.get_generic_param_type(sym.as_str()).unwrap())
                }
                Type::QPath(qpathdata) => {
                    // FIXME: currently we ignore assoc item
                    println!("[Solver] ignore QPath {:?}", type_);
                    continue;
                }
                _ => self.get_type_impls(type_),
            };

            if let Some(impl_set) = self.extract_type_impls_with_bounds(tuple, bounds) {
                set_union(&mut visited, &impl_set);
            } else {
                return false;
            }
        }

        // let callable = self.get_current_callable_type();

        /* if (callable.is_subset(&self.all_callable)) {
            return false;
        } */
        if (!self.is_current_callable()) {
            return false;
        }
        // if visited is empty, there is no bound for type
        if (!visited.is_empty() && visited.is_subset(&self.all_visited)) {
            return false;
        }
        // set_union(&mut self.all_callable, &callable);
        set_union(&mut self.all_visited, &visited);
        println!("[Solver] select combination {}", self.display_combination());
        println!("[Solver] visited={:?}", visited);
        true
    }

    fn is_num_enough(&self) -> bool {
        // return false;
        return self.solution_count >= MAX_MONO_PER_FUNC;
    }

    fn search(&mut self, param_no: usize) {
        let len = self.type_context.borrow().get_sorted_type().len();
        if param_no >= self.generic_param.len() {
            self.try_count+=1;
            if !self.is_num_enough() && self.check_pred() {
                self.solution_count += 1;
                let func = self.make_function();
                println!("[Solver] find solutions: {}", func._pretty_print());
                self.solutions.push(func);
            }
            return;
        }

        // dfs searching
        for i in 0..len {
            self.current[param_no] = i;
            if self.try_count<500000 && !self.is_num_enough(){
                self.search(param_no + 1);
            }
            
        }
    }

    pub(crate) fn solve(&mut self) {
        println!(
            "[Solver] find solution for {}, already have {} solutions",
            self.current_function.api_function._pretty_print(),
            self.solution_count
        );
        println!("[Solver] generic params: {:?}", self.generic_param);
        //self.print_all_candidates();
        if self.generic_param.len() >= 4 {
            println!("[Solver] Skip it. Too many generic params! This might be slow.");
        }
        if !self.solvable {
            println!("[Solver] Skip it. it is unsolvable.");
        }
        if self.is_num_enough() {
            println!("[Solver] Skip it. it have enough solutions.");
        }
        if self.generic_param.len()==0{
            println!("[Solver] Skip it. no bounded parameter.");
        }

        if !self.is_num_enough() && self.solvable && self.generic_param.len() < 4 && self.generic_param.len() >0
        {
            let now = Instant::now();
            let len = self.generic_param.len();
            self.current.resize(len, 0);
            self.try_count=0;

            println!("[Solver] Start solve()");
            self.search(0);
            let elapsed_time = now.elapsed();
            println!("[Solver] try {} combinations",self.try_count);
            println!("[Solver] Running solve() took {} ms.", elapsed_time.as_millis());
        }
    }

    pub(crate) fn take_solutions(&mut self) -> Vec<ApiFunction> {
        let mut res = Vec::new();
        while let Some(func) = self.solutions.pop() {
            res.push(func);
        }
        res
    }
}
