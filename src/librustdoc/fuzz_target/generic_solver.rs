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
use std::cmp::Eq;
use std::hash::Hash;
use std::time::Instant;
use std::{cell::RefCell, rc::Rc};

use super::trait_impl::TraitImplMap;

static MAX_MONO_PER_FUNC: usize = 3;
static MAX_TYPE_DEPTH: usize = 3;

pub(crate) struct GenericSolver<'a> {
    current: Vec<usize>,
    current_type: Vec<Type>,
    current_function: &'a GenericFunction,
    all_visited: FxHashSet<DefId>, // set of impl id
    all_callable: FxHashSet<(i32, i32)>,
    type_context: Rc<RefCell<TypeContext>>,
    trait_impl_map: &'a TraitImplMap,
    cache: &'a Cache,
    full_name_map: &'a FullNameMap,
    solutions: Vec<ApiFunction>,
    solution_count: usize,
    solvable: bool,
    try_count: usize,
}

impl<'a> GenericSolver<'a> {
    pub(crate) fn new(
        cache: &'a Cache,
        full_name_map: &'a FullNameMap,
        type_context: Rc<RefCell<TypeContext>>,
        trait_impl_map: &'a TraitImplMap,
        generic_function: &'a GenericFunction,
    ) -> GenericSolver<'a> {
        let len = generic_function.bounded_symbols.len();
        let solvable = generic_function.generic_map.is_solvable();

        // println!("[Solver] generic_param: {:?}", generic_param);
        GenericSolver {
            all_callable: FxHashSet::<(i32, i32)>::default(),
            type_context,
            trait_impl_map,
            current: Vec::new(),
            current_type: Vec::new(),
            current_function: generic_function,
            all_visited: FxHashSet::<DefId>::default(),
            solutions: Vec::new(),
            cache,
            full_name_map,
            solvable,
            solution_count: 0,
            try_count: 0,
        }
    }

    /* fn make_function(&self) -> ApiFunction {
        let mut func = self.current_function.api_function.clone();
        func.mono = true;

        for type_ in &mut func.inputs {
            *type_ = self.replace_generic(type_);
        }
        if let Some(ref output) = func.output {
            func.output = Some(self.replace_generic(output));
        }
        func
    } */

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
        // return false;
        return self.solution_count >= MAX_MONO_PER_FUNC;
    }

    /* fn dfs(&mut self, param_no: usize) {
        let len = self.type_context.borrow().get_sorted_type().len();
        if param_no >= self.generic_param.len() {
            self.try_count += 1;
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
            self.current[param_no] = i; // TODO: workaround
            if self.try_count < 500000 && !self.is_num_enough() {
                self.dfs(param_no + 1);
            }
        }
    } */

    fn search(&mut self) {
        let mut solution_set = Vec::<Solution>::new();
        solution_set.push(vec![Type::Infer; self.current_function.generic_map.generic_defs.len()]);
        // get reachable solution set
        for pat in self.current_function.api_function.inputs.iter() {
            if !is_generic_type(pat) {
                continue;
            }
            println!("[Solver] search for input argument {}:", _type_name(pat, None));
            let mut sols = FxHashSet::<Solution>::default();
            for src in self.type_context.borrow().get_sorted_type().iter() {
                if let Some(sol) =
                    match_call_type(src, pat, &self.current_function.generic_map.generic_defs)
                {
                    /* println!(
                        "{} and {} is matched: {:?}",
                        _type_name(src, None),
                        _type_name(pat, None),
                        sol
                    ); */
                    if check_solution_depth(&sol, MAX_TYPE_DEPTH) {
                        sols.insert(sol);
                    }
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
                    println!("[Solver] solution mark as unsolvable",);
                    return;
                }
            }
            println!("[Solver] Check Solution: {}", solution_string(&solution));
            if self.current_function.generic_map.check_solution(
                &solution,
                self.trait_impl_map,
                self.cache,
            ) {
                valid_solution_set.push(solution);
            }
        }

        for solution in valid_solution_set {
            self.solution_count += 1;
            let func = self.make_function_with(&solution);
            println!("[Solver] find solutions: {}", func._pretty_print());
            self.solutions.push(func);
        }
    }

    pub(crate) fn solve(&mut self) {
        println!(
            "[Solver] find solution for {}, already have {} solutions",
            self.current_function.api_function._pretty_print(),
            self.solution_count
        );
        println!("[Solver] generic params: {:?}", self.current_function.generic_map.generic_defs);
        //self.print_all_candidates();
        /* if self.generic_param.len() >= 4 {
            println!("[Solver] Skip it. Too many generic params! This might be slow.");
            return;
        } */
        if !self.solvable {
            println!("[Solver] Skip it. it is unsolvable.");
            return;
        }
        if self.is_num_enough() {
            println!("[Solver] Skip it. it have enough solutions.");
            return;
        }
        let len = self.current_function.generic_map.generic_defs.len();
        if len == 0 {
            println!("[Solver] Skip it. no bounded parameter.");
            return;
        }

        let now = Instant::now();

        self.current.resize(len, 0);
        self.current_type.resize(len, Type::Infer);
        self.try_count = 0;

        println!("[Solver] Start solve()");
        self.search();
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
