use crate::clean::{GenericArg, GenericArgs};
use crate::clean::{Path, Type};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_graph::{any_type_match, ApiGraph, TypeContext};
use crate::fuzz_target::api_util::{
    self, _type_name, is_generic_type, is_support_type, replace_type_with, type_depth,
};
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::generic_param_map::set_union;
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::generic_solution::*;
use crate::fuzz_target::impl_id::ImplId;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::statistic;
use crate::fuzz_target::trait_impl::{TraitImpl,TypeTraitCache};
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::borrow::BorrowMut;
use std::cmp::Eq;
use std::hash::Hash;
use std::time::Instant;
use std::{cell::RefCell, rc::Rc};

use super::trait_impl::TraitImplMap;

static MAX_MONO_PER_FUNC: usize = 100;
pub static MAX_TYPE_DEPTH: usize = 4;

pub(crate) struct GenericSolver {
    current: Vec<usize>,
    pub current_function: GenericFunction,
    diverse_set: FxHashSet<ImplId>,
    reserved: Vec<bool>,
    reachable_inputs: Vec<bool>,
    contain_generic: Vec<bool>,
    type_context: Rc<RefCell<TypeContext>>,
    solutions: Vec<(Solution, ApiFunction, FxHashSet<ImplId>)>,
    solution_set: FxHashSet<Solution>,
    solution_count: usize,
    solvable: bool,
    success: bool,
    try_count: usize,
}

impl GenericSolver {
    pub(crate) fn new(
        type_context: Rc<RefCell<TypeContext>>,
        generic_function: GenericFunction,
    ) -> GenericSolver {
        let mut solvable = generic_function.is_solvable();
        let len = generic_function.api_function.inputs.len();
        let mut contain_generic = vec![false; len];

        for (i, input) in generic_function.api_function.inputs.iter().enumerate() {
            if !is_support_type(input) {
                println!("[Solver] {} is unsupported", _type_name(input, None));

                solvable = false;
            }
            contain_generic[i] = is_generic_type(input);
        }
        // println!("[Solver] generic_param: {:?}", generic_param);
        GenericSolver {
            type_context,
            current: Vec::new(),
            current_function: generic_function,
            reachable_inputs: vec![false; len],
            contain_generic,
            diverse_set: FxHashSet::<ImplId>::default(),
            reserved: Vec::new(),
            solutions: Vec::new(),
            solution_set: FxHashSet::<Solution>::default(),
            solvable,
            solution_count: 0,
            try_count: 0,
            success: false,
        }
    }

    pub(crate) fn num_solution(&self) -> usize {
        self.solutions.len()
    }

    fn make_function_with(&self, solution: &Solution) -> ApiFunction {
        let mut func = self.current_function.api_function.clone();
        let generic_defs = &self.current_function.generic_map.generic_defs;
        func.mono = true;
        for type_ in &mut func.inputs {
            replace_generic_with_solution(type_, solution, generic_defs);
        }
        if let Some(ref mut output) = func.output {
            replace_generic_with_solution(output, solution, generic_defs);
        }
        if let Some(ref mut self_) = func.self_ {
            replace_generic_with_solution(self_, solution, generic_defs);
        }
        if let Some(ref mut trait_) = func.trait_ {
            replace_generic_with_solution(trait_, solution, generic_defs);
        }
        func
    }

    fn is_num_enough(&self) -> bool {
        // return false; // never enough
        return self.solution_count >= MAX_MONO_PER_FUNC;
    }

    fn dfs(
        &mut self,
        solution: &mut Solution,
        no: usize,
        cache: &Cache,
        trait_impl_map: &TraitImplMap,
        type_trait_cache: &mut TypeTraitCache, 
    ) {
        // check unsolvable
        if self.is_num_enough() || !self.solvable {
            return;
        }
        
        if no >= self.current.len() {
            println!("[Solver] Check Solution: {}", solution_string(&solution));
            if let Some(impl_set) =
                self.current_function.generic_map.check_solution(&solution, trait_impl_map, type_trait_cache, cache)
            {
                //valid_solution_set.push(solution);
                let func = self.make_function_with(&solution);
                println!("[Solver] find mono function: {}", func._pretty_print(cache));
                println!("[Solver] mono solution: {:?}", solution);
                println!("[Solver] impls={:?}", impl_set);
                if let Some(ref output) = func.output {
                    let depth = type_depth(output);
                    println!("[Solver] output depth = {}", depth);
                    if depth > MAX_TYPE_DEPTH {
                        println!("[Solver] solution is refused because output is too deep.");
                        return;
                    }
                }
                if let Some(ref output) = func.output {
                    RefCell::borrow_mut(&self.type_context).add_canonical_types(output, cache);
                }
                self.solution_count += 1;
                self.solutions.push((solution.to_vec(), func, impl_set));
                self.reserved.push(false);
                self.success = true;
            }
            return;
        }

        if let Type::Infer = solution[no] {
            /* for ty in trait_impl_map.concrete_iter(){
                solution[no] = ty.clone();
                self.dfs(solution, no + 1, cache, trait_impl_map, type_trait_cache);
            } */
            self.solvable = false;
            println!("[Solver] mark function as unsolvable");
            return;
        }

        // if solution[no] is a concrete type, goto next one
        self.dfs(solution, no + 1, cache, trait_impl_map, type_trait_cache);
    }

    fn search(&mut self, cache: &Cache, trait_impl_map: &TraitImplMap, type_trait_cache:&mut TypeTraitCache) -> bool {
        let mut solution_set = Vec::<Solution>::new();
        solution_set.push(vec![Type::Infer; self.current_function.generic_map.generic_defs.len()]);
        // get reachable solution set
        for (i, pat) in self.current_function.api_function.inputs.iter().enumerate() {
            if !self.contain_generic[i] {
                continue;
            }
            println!("[Solver] search for input argument {}:", _type_name(pat, None));
            let mut sols = FxHashSet::<Solution>::default();
            for src in self.type_context.borrow().type_candidates.keys() {
                if let Some(sol) = match_call_type(
                    src,
                    pat,
                    &self.current_function.generic_map.generic_defs,
                    cache,
                ) {
                    /* println!(
                        "{} and {} is matched: {:?}",
                        _type_name(src, None),
                        _type_name(pat, None),
                        sol
                    ); */
                    sols.insert(sol);
                }
            }
            let sols = sols.into_iter().collect();
            solution_set = merge_solution_set(
                &solution_set,
                &sols,
                &self.current_function.generic_map.generic_defs,
            );
        }

        println!("[Solver] Solution Set = {}", solution_set_string(&solution_set));

        // check type predicate
        self.success = false;
        for mut solution in solution_set.into_iter() {
            // prevent duplicate
            if self.solution_set.get(&solution).is_some() {
                continue;
            }
            self.solution_set.insert(solution.clone());

            self.dfs(&mut solution, 0, cache, trait_impl_map, type_trait_cache);
        }
        self.success
    }
    pub(crate) fn is_solvable(&self) -> bool {
        self.solvable
    }

    pub(crate) fn check_reachable(&mut self, full_name_map: &FullNameMap, cache: &Cache) -> bool {
        let mut success = true;
        for (i, type_) in self.current_function.api_function.inputs.iter().enumerate() {
            if !self.contain_generic[i] && !self.reachable_inputs[i] {
                self.reachable_inputs[i] =
                    self.type_context.borrow().is_callable(type_, full_name_map, cache);
                if !self.reachable_inputs[i] {
                    println!(
                        "[Solver] input#{}: {} is unreachable",
                        i,
                        _type_name(type_, Some(cache))
                    );
                    success = false;
                }
            }
        }
        success
    }

    pub(crate) fn solve(
        &mut self,
        cache: &Cache,
        trait_impl_map: &TraitImplMap,
        type_trait_cache: &mut TypeTraitCache, 
        full_name_map: &FullNameMap,
    ) {
        println!(
            "[Solver] find solution for {}, already have {} solutions",
            self.current_function.api_function._pretty_print(cache),
            self.solution_count
        );
        println!("[Solver] generic params: {:?}", self.current_function.generic_map.generic_defs);

        /* if self.generic_param.len() >= 4 {
            println!("[Solver] Skip it. Too many generic params! This might be slow.");
            return;
        } */

        if !self.solvable {
            println!("[Solver] Skip it. It is unsolvable.");
            return;
        }
        if self.is_num_enough() {
            println!("[Solver] Skip it. It have enough solutions.");
            return;
        }
        if !self.check_reachable(full_name_map, cache) {
            println!("[Solver] Skip it. It is currently unreachable.");
            return;
        }

        let len = self.current_function.generic_map.generic_defs.len();
        if len == 0 {
            unreachable!("This is not a generic function");
            println!("[Solver] Skip it. no type parameter.");
            return;
        }

        let now = Instant::now();

        self.current.resize(len, 0);
        self.try_count = 0;

        println!("[Solver] Start solve()");
        self.search(cache, trait_impl_map, type_trait_cache);
        let elapsed_time = now.elapsed();
        // println!("[Solver] try {} combinations", self.try_count);
        println!("[Solver] Running solve() took {} ms.", elapsed_time.as_millis());
    }

    pub(crate) fn propagate_reserve(
        &mut self,
        diverse_types: &mut FxHashMap<Type, bool>,
        full_name_map: &FullNameMap,
        cache: &Cache,
    ) -> bool {
        let mut success = false;
        for i in 0..self.num_solution() {
            if self.reserved[i] {
                continue;
            }
            let impl_set = &self.solutions[i].2;
            if let Some(ref output) = self.solutions[i].1.output {
                if any_type_match(diverse_types, output, full_name_map, cache, true) {
                    self.reserve(i,diverse_types,cache);
                    success = true;
                }
            }
        }
        success
    }

    pub(crate) fn init_diverse_set(
        &mut self,
        diverse_types: &mut FxHashMap<Type, bool>,
        cache: &Cache,
    ) {
        println!(
            "[Solver] init diverse solution for {}",
            self.current_function.api_function._pretty_print(cache)
        );
        let diverse_count = |a: &FxHashSet<ImplId>, b: &FxHashSet<ImplId>| -> usize {
            let mut cnt = 0;
            for id in a.iter() {
                if b.get(id).is_none() {
                    cnt += 1;
                }
            }
            cnt
        };

        // greedy algorithm. Choose solution of maximum uncovered id
        loop {
            let mut max_id = 0;
            let mut max_num = 0;
            for i in 0..self.num_solution() {
                if !self.reserved[i] {
                    let num = diverse_count(&self.solutions[i].2, &self.diverse_set);
                    if num > max_num {
                        max_id = i;
                        max_num = num;
                    }
                }
            }

            if max_num == 0 {
                break;
            }

            self.reserve(max_id, diverse_types, cache);
        }

        self.reserve_least_one(diverse_types, cache);
    }

    pub(crate) fn reserve(&mut self, no:usize, diverse_types:&mut FxHashMap<Type, bool>, cache: &Cache){
        println!(
            "[Solver] reserve mono: {}, {:?}, all={:?}",
            &self.solutions[no].1._pretty_print(cache),
            self.solutions[no].2,
            self.diverse_set
        );
        set_union(&mut self.diverse_set, &self.solutions[no].2);
        self.reserved[no] = true;
        for input in self.solutions[no].1.inputs.iter() {
            if diverse_types.get(input).is_none() {
                diverse_types.insert(input.clone(), false);
            }
        }
    }

    /// make sure at least one solution is selected
    pub(crate) fn reserve_least_one(&mut self, diverse_types:&mut FxHashMap<Type, bool>, cache: &Cache) {
        if self.num_solution() == 0 {
            return;
        }
        for i in 0..self.num_solution() {
            if self.reserved[i] {
                return;
            }
        }
        self.reserve(0, diverse_types, cache);
    }

    pub(crate) fn reserve_solutions(&self) -> Vec<ApiFunction> {
        let mut res = Vec::new();
        for i in 0..self.num_solution() {
            if self.reserved[i] {
                res.push(self.solutions[i].1.clone());
            }
        }
        res
    }

    pub(crate) fn take_solutions(&mut self) -> Vec<(ApiFunction, bool, FxHashSet<ImplId>)> {
        let mut res = Vec::new();
        let mut ind = self.solutions.len() - 1;
        while let Some((_, func, impl_set)) = self.solutions.pop() {
            res.push((func, self.reserved[ind], impl_set));
            ind -= 1;
        }
        res
    }
}
