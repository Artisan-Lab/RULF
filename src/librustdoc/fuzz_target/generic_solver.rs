use crate::clean::{GenericArg, GenericArgs};
use crate::clean::{Path, Type};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_graph::{ApiGraph, TypeContext};
use crate::fuzz_target::api_util::{
    self, _type_name, is_generic_type, replace_type_with, type_depth,
};
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::generic_solution::*;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::statistic;
use crate::fuzz_target::trait_impl::TraitImpl;
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::borrow::BorrowMut;
use std::cmp::Eq;
use std::hash::Hash;
use std::time::Instant;
use std::{cell::RefCell, rc::Rc};

use super::trait_impl::TraitImplMap;

static MAX_MONO_PER_FUNC: usize = 3;
static MAX_TYPE_DEPTH: usize = 5;

pub(crate) struct GenericSolver {
    current: Vec<usize>,
    current_function: GenericFunction,
    all_visited: FxHashSet<DefId>, // set of impl id
    all_callable: FxHashSet<(i32, i32)>,
    reachable_inputs: Vec<bool>,
    contain_generic: Vec<bool>,
    type_context: Rc<RefCell<TypeContext>>,
    solutions: Vec<ApiFunction>,
    solution_set: FxHashSet<Solution>,
    solution_count: usize,
    solvable: bool,
    try_count: usize,
}

impl GenericSolver {
    pub(crate) fn new(
        type_context: Rc<RefCell<TypeContext>>,
        generic_function: GenericFunction,
    ) -> GenericSolver {
        let solvable = generic_function.generic_map.is_solvable();
        let len = generic_function.api_function.inputs.len();
        let mut contain_generic = vec![false; len];

        for (i, input) in generic_function.api_function.inputs.iter().enumerate() {
            contain_generic[i] = is_generic_type(input);
        }
        // println!("[Solver] generic_param: {:?}", generic_param);
        GenericSolver {
            all_callable: FxHashSet::<(i32, i32)>::default(),
            type_context,
            current: Vec::new(),
            current_function: generic_function,
            reachable_inputs: vec![false; len],
            contain_generic,
            all_visited: FxHashSet::<DefId>::default(),
            solutions: Vec::new(),
            solution_set: FxHashSet::<Solution>::default(),
            solvable,
            solution_count: 0,
            try_count: 0,
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
            *type_ = replace_generic_with_solution(type_, solution, generic_defs);
        }
        if let Some(ref output) = func.output {
            func.output = Some(replace_generic_with_solution(output, solution, generic_defs));
        }
        func
    }

    fn is_num_enough(&self) -> bool {
        return false; // never enough
        return self.solution_count >= MAX_MONO_PER_FUNC;
    }

    fn search(&mut self, cache: &Cache, trait_impl_map: &TraitImplMap) -> bool {
        let mut success = false;
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
        let mut valid_solution_set = Vec::<Solution>::new();
        for solution in solution_set.into_iter() {
            for i in 0..self.current.len() {
                if let Type::Infer = solution[i] {
                    self.solvable = false;
                    println!("[Solver] solution mark as unsolvable");
                    return false;
                }
            }
            if self.solution_set.get(&solution).is_some() {
                continue;
            }
            self.solution_set.insert(solution.clone());

            println!("[Solver] Check Solution: {}", solution_string(&solution));
            if self.current_function.generic_map.check_solution(&solution, trait_impl_map, cache) {
                valid_solution_set.push(solution);
            }
        }

        for solution in valid_solution_set {
            let func = self.make_function_with(&solution);
            println!("[Solver] find mono function: {}", func._pretty_print(cache));
            if let Some(ref output) = func.output {
                let depth = type_depth(output);
                println!("[Solver] output depth = {}", depth);
                if depth > MAX_TYPE_DEPTH {
                    println!("[Solver] solution is refused because output is too deep.");
                    continue;
                }
            }
            if let Some(ref output) = func.output {
                RefCell::borrow_mut(&self.type_context).add_type_candidate(output);
            }

            self.solution_count += 1;
            self.solutions.push(func);
            success = true;
        }
        success
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
        full_name_map: &FullNameMap,
    ) {
        println!(
            "[Solver] find solution for {}, already have {} solutions",
            self.current_function.api_function._pretty_print(cache),
            self.solution_count
        );
        println!("[Solver] generic params: {:?}", self.current_function.generic_map.generic_defs);
        //self.print_all_candidates();
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
            println!("[Solver] Skip it. no bounded parameter.");
            return;
        }

        let now = Instant::now();

        self.current.resize(len, 0);
        self.try_count = 0;

        println!("[Solver] Start solve()");
        self.search(cache, trait_impl_map);
        let elapsed_time = now.elapsed();
        // println!("[Solver] try {} combinations", self.try_count);
        println!("[Solver] Running solve() took {} ms.", elapsed_time.as_millis());
    }

    pub(crate) fn take_solutions(&mut self) -> Vec<ApiFunction> {
        let mut res = Vec::new();
        while let Some(func) = self.solutions.pop() {
            res.push(func);
        }
        res
    }
}
