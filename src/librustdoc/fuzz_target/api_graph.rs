use super::api_util::is_fuzzable_type;
use super::api_util::is_support_type;
use super::api_util::replace_type_with;
use super::trait_impl::TraitImplMap;
use crate::clean::GenericArgs;
use crate::clean::Generics;
use crate::clean::Path;
use crate::clean::PrimitiveType;
use crate::clean::Struct;
use crate::clean::Type;
use crate::clean::Visibility;
use crate::clean::{GenericArg, Lifetime};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_sequence::{ApiCall, ApiSequence, ParamType};
use crate::fuzz_target::api_util;
use crate::fuzz_target::api_util::{_type_name, get_type_name_from_did, replace_lifetime, _same_type};
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzz_target_renderer::FuzzTargetContext;
use crate::fuzz_target::fuzzable_type;
use crate::fuzz_target::fuzzable_type::FuzzableType;
use crate::fuzz_target::generic_function;
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::generic_solution::take_type_from_path;
use crate::fuzz_target::generic_solver;
use crate::fuzz_target::generic_solver::GenericSolver;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::mod_visibility::ModVisibity;
use crate::fuzz_target::prelude_type;
use crate::fuzz_target::statistic;
use crate::fuzz_target::trait_impl::{TraitImpl, TypeTraitCache};
use crate::html::format::join_with_double_colon;
use crate::TyCtxt;
use lazy_static::lazy_static;
use rand::{self, Rng};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_hir::Mutability;
use std::cmp::{max, min};
use std::collections::VecDeque;
use std::{cell::RefCell, rc::Rc};

lazy_static! {
    static ref RANDOM_WALK_STEPS: FxHashMap<&'static str, usize> = {
        let mut m = FxHashMap::default();
        m.insert("regex", 10000);
        m.insert("url", 10000);
        m.insert("time", 10000);
        m
    };
}

/* fn add_func_input_to_set(type_set: &mut FxHashSet<Type>, func: &ApiFunction) {
    for input in func.inputs.iter() {
        type_set.insert(input.clone());
    }
} */


fn print_diverse_types(diverse_types:&FxHashMap::<Type, bool>){
    println!("===== diverse types =====");
    for (ty,visit) in diverse_types.iter(){
        println!("{}: {}",_type_name(ty,None), visit);
    }
    println!("===== !diverse types =====");
}

pub(crate) fn any_type_match(
    type_map: &mut FxHashMap<Type, bool>,
    type_: &Type,
    full_name_map: &FullNameMap,
    cache: &Cache,
    ignore_reachable: bool,
) -> bool {
    let mut success = false;
    for (input, val) in type_map.iter_mut() {
        if ignore_reachable && *val {
            continue;
        }
        if api_util::_same_type(type_, input, true, full_name_map, cache).is_compatible() {
            success = true;
            *val = true;
        }
    }
    success
}

pub(crate) struct TypeContext {
    pub(crate) trait_type: FxHashSet<Type>,
    pub(crate) type_candidates: FxHashMap<Type, usize>,
    pub(crate) type_sorted: Vec<Type>,
    pub(crate) functions: Vec<ApiFunction>,
}

impl TypeContext {
    pub(crate) fn new() -> TypeContext {
        let mut tc = TypeContext {
            trait_type: FxHashSet::default(),
            type_candidates: FxHashMap::<Type, usize>::default(),
            type_sorted: Vec::new(),
            functions: Vec::new(),
        };
        tc.add_prelude_type();
        tc
    }

    pub(crate) fn add_trait_type(&mut self, type_: &Type) {
        self.trait_type.insert(type_.clone());
    }

    fn add_prelude_type(&mut self) {
        // add u8
        self.add_type_candidate(&Type::Primitive(PrimitiveType::U8));
        // add &[u8]
        self.add_type_candidate(&Type::BorrowedRef {
            type_: Box::new(Type::Slice(Box::new(Type::Primitive(PrimitiveType::U8)))),
            lifetime: None,
            mutability: Mutability::Not,
        });
        /* self.add_type_candidate(&Type::BorrowedRef {
            lifetime: None,
            mutability: Mutability::Mut,
            type_: Box::new(Type::Slice(Box::new(Type::Primitive(PrimitiveType::U8)))),
        }); */
    }

    pub(crate) fn get_sorted_type(&self) -> &Vec<Type> {
        &self.type_sorted
    }

    pub(crate) fn print_all_candidates(&self, cache: &Cache) {
        let mut count = 0;
        for (ty, freq) in self.type_candidates.iter() {
            println!("Type Candidate #{}: ({}){}", count, freq, _type_name(ty, Some(cache)));
            count += 1;
        }
    }

    pub(crate) fn add_type_candidate(&mut self, type_: &Type) -> bool {
        if let Some(v) = self.type_candidates.get_mut(type_) {
            *v += 1;
            false
        } else {
            if api_util::type_depth(type_) > generic_solver::MAX_TYPE_DEPTH
                || !is_support_type(type_)
            {
                return false;
            }
            let no = self.type_candidates.len();
            statistic::inc("CANDIDATES");
            println!(
                "[TypeContext] add candidate #{}: {} => {:?}",
                no,
                _type_name(&type_, None),
                type_
            );
            self.type_candidates.insert(type_.clone(), 1);
            true
        }
    }

    pub(crate) fn add_canonical_types(&mut self, type_: &Type, cache: &Cache) {
        self.add_type_candidate(type_);
        // add transformed type: &mut A, &A, *const T, *T
        self.add_type_candidate(&Type::BorrowedRef {
            lifetime: None,
            type_: Box::new(type_.clone()),
            mutability: Mutability::Mut,
        });
        self.add_type_candidate(&Type::BorrowedRef {
            lifetime: None,
            type_: Box::new(type_.clone()),
            mutability: Mutability::Not,
        });
        self.add_type_candidate(&Type::RawPointer(Mutability::Mut, Box::new(type_.clone())));
        self.add_type_candidate(&Type::RawPointer(Mutability::Not, Box::new(type_.clone())));

        match type_ {
            Type::Path { ref path } => {
                let name = get_type_name_from_did(path.def_id(), cache);
                // let name = path.segments.last().unwrap().name.to_string();
                let inner = if name == "core::option::Option" {
                    take_type_from_path(path, 0)
                } else if name == "core::result::Result" {
                    take_type_from_path(path, 0)
                } else {
                    return;
                };
                self.add_canonical_types(&inner, cache);
            }
            Type::Tuple(ref types) => {
                for ty_ in types {
                    self.add_canonical_types(ty_, cache);
                }
            }
            _ => {}
        }
    }

    pub(crate) fn is_callable(
        &self,
        type_: &Type,
        full_name_map: &FullNameMap,
        cache: &Cache,
    ) -> bool {
        if is_fuzzable_type(type_, full_name_map, cache) {
            return true;
        }

        for (reachable_type, num) in self.type_candidates.iter() {
            /* print!(
                "Check {} to {} =>",
                _type_name(reachable_type, Some(cache)),
                _type_name(type_, Some(cache))
            ); */
            if _type_name(reachable_type, Some(cache)) == _type_name(type_, Some(cache)) {
                // print!("True\n");
                return true;
            }

            if _same_type(reachable_type, type_, true, full_name_map, cache)
                .is_compatible()
            {
                // print!("True\n");
                return true;
            }
            // print!("False\n");
        }

        false
    }

    pub(crate) fn update_sorted_type(&mut self) {
        let mut vec = self.type_candidates.iter().collect::<Vec<_>>();
        vec.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        self.type_sorted = vec.into_iter().map(|a| a.0.clone()).collect();
    }
}

pub(crate) struct ApiGraph<'tcx> {
    pub(crate) _crate_name: String,
    pub(crate) api_functions: Vec<ApiFunction>,
    pub(crate) reachable: Vec<bool>,
    pub(crate) reachable_input: Vec<Vec<bool>>,
    pub(crate) unreachable_num: Vec<usize>,
    pub(crate) reserve: Vec<bool>,
    pub(crate) api_functions_visited: Vec<bool>,
    pub(crate) api_dependencies: Vec<ApiDependency>,
    pub(crate) api_sequences: Vec<ApiSequence>,
    pub(crate) trait_impl_map: TraitImplMap, // type defid => {(trait path, generics, impl id)}
    pub(crate) full_name_map: FullNameMap,   //did to full_name
    pub(crate) mod_visibility: ModVisibity, //the visibility of mods，to fix the problem of `pub(crate) use`
    pub(crate) generic_functions: Vec<GenericFunction>,
    pub(crate) functions_with_unsupported_fuzzable_types: FxHashSet<String>,
    pub(crate) type_context: Rc<RefCell<TypeContext>>,
    pub(crate) cx: Rc<FuzzTargetContext<'tcx>>, 
}

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum GraphTraverseAlgorithm {
    _Bfs,
    _FastBfs,
    _BfsEndPoint,
    _FastBfsEndPoint,
    _RandomWalk,
    _RandomWalkEndPoint,
    _TryDeepBfs,
    _DirectBackwardSearch,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Copy)]
pub(crate) enum ApiType {
    BareFunction,
    // MonoFunction,
}

type Solution = FxHashMap<String, Vec<Type>>; // TODO: Type or DefId?
//函数的依赖关系
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub(crate) struct ApiDependency {
    pub(crate) output_fun: (ApiType, usize), //the index of first func
    pub(crate) input_fun: (ApiType, usize),  //the index of second func
    pub(crate) input_param_index: usize,
    pub(crate) call_type: CallType,
}

impl<'tcx> ApiGraph<'tcx> {
    pub(crate) fn new(_crate_name: String, cx: Rc<FuzzTargetContext<'tcx>>) -> Self {
        ApiGraph {
            api_functions: Vec::new(),
            api_functions_visited: Vec::new(),
            api_dependencies: Vec::new(),
            api_sequences: Vec::new(),
            reachable: Vec::new(),
            reachable_input: Vec::new(),
            unreachable_num: Vec::new(),
            reserve: Vec::new(),
            type_context: Rc::new(RefCell::new(TypeContext::new())),
            trait_impl_map: TraitImplMap::new(),
            full_name_map: FullNameMap::new(),
            mod_visibility: ModVisibity::new(&_crate_name),
            generic_functions: Vec::new(),
            functions_with_unsupported_fuzzable_types: FxHashSet::default(),
            _crate_name,
            cx,
        }
    }

    pub fn print_unsupport_function(&self) {
        println!("unsupport function:");
        for name in self.functions_with_unsupported_fuzzable_types.iter() {
            println!("{}", name);
        }
    }

    pub fn get_full_path_from_def_id(&self, did: DefId) -> String {
        if let Some(&(ref syms, item_type)) = self.cache().paths.get(&did) {
            join_with_double_colon(syms)
        } else if let Some(&(ref syms, item_type)) = self.cache().external_paths.get(&did) {
            join_with_double_colon(syms)
        } else {
            panic!("did could not be found in cache")
        }
    }

    pub(crate) fn cache(&self) -> &Cache {
        &self.cx.cache
    }

    pub(crate) fn tcx(&self) -> TyCtxt<'tcx> {
        self.cx.tcx
    }

    pub(crate) fn print_full_name_map(&self) {
        for (did, (full_name, _)) in self.full_name_map.map.iter() {
            println!("{:?} => {}", did, full_name);
        }
    }

    pub(crate) fn print_type_candidates(&self) {
        self.type_context.borrow().print_all_candidates(self.cache());
    }

    pub(crate) fn print_type_trait_impls(&self) {
        for (did, vec_trait_impls) in &self.trait_impl_map.inner {
            println!(
                "\ntype {} implement {} traits: ",
                &self.full_name_map.get_full_name(*did).unwrap(),
                vec_trait_impls.len()
            );
            for trait_impl in vec_trait_impls.iter() {
                let trait_ = &trait_impl.trait_;
                let bounds = &trait_impl.generic_map;
                let impl_id = trait_impl.impl_id;
                let ty = Type::Path { path: trait_.clone() };
                println!(
                    "{:?}: impl {} for {}\nbounds: {:?}",
                    impl_id,
                    _type_name(&ty, Some(self.cache())),
                    _type_name(&trait_impl.for_, Some(self.cache())),
                    bounds
                );
            }
        }
    }

    pub(crate) fn update_candidate_types(&mut self) {
        let num_func = self.api_functions.len();
        println!("num of func: {}", num_func);
        println!("num of reachable: {}", self.reachable.len());
        println!("num of reachable type: {}", self.reachable_input.len());
        let mut que = VecDeque::<usize>::new();
        for i in 0..num_func {
            if !self.reachable[i] {
                for j in 0..self.api_functions[i].inputs.len() {
                    let input = &self.api_functions[i].inputs[j];
                    if !self.reachable_input[i][j]
                        && self.type_context.borrow().is_callable(
                            input,
                            &self.full_name_map,
                            self.cache(),
                        )
                    {
                        self.reachable_input[i][j] = true;
                        self.unreachable_num[i] -= 1;
                    }
                }
                if self.unreachable_num[i] == 0 {
                    que.push_back(i);
                    self.reachable[i] = true;
                    println!(
                        "[Reachable]{} is reachable",
                        self.api_functions[i]._pretty_print(self.cache())
                    );
                    if let Some(ref output) = self.api_functions[i].output {
                        self.type_context.borrow_mut().add_canonical_types(output, self.cache());
                    }
                }
            }
        }

        while let Some(id) = que.pop_front() {
            if let Some(ref output) = self.api_functions[id].output {
                self.type_context.borrow_mut().add_canonical_types(output, self.cache());

                for i in 0..num_func {
                    if !self.reachable[i] {
                        for j in 0..self.api_functions[i].inputs.len() {
                            let input = &self.api_functions[i].inputs[j];
                            if api_util::_same_type(
                                output,
                                input,
                                true,
                                &self.full_name_map,
                                self.cache(),
                            )
                            .is_compatible()
                            {
                                self.reachable_input[i][j] = true;
                                self.unreachable_num[i] -= 1;
                            }
                        }
                        if self.unreachable_num[i] == 0 {
                            que.push_back(i);
                            println!(
                                "[Reachable]{} is reachable",
                                self.api_functions[i]._pretty_print(self.cache())
                            );
                            self.reachable[i] = true;
                        }
                    }
                }
            }
        }

        self.type_context.borrow_mut().update_sorted_type();
    }

    pub(crate) fn update_reachable_info(&mut self) {
        let start = self.reachable.len();
        let end = self.api_functions.len();
        for i in start..end {
            let api_fun = &self.api_functions[i];
            self.reachable.push(false);
            self.reachable_input.push(vec![false; api_fun.inputs.len()]);
            self.reserve.push(false);
            self.unreachable_num.push(api_fun.inputs.len());
        }
    }

    pub(crate) fn update_reserve(&mut self, diverse_types: &mut FxHashMap<Type, bool>){
        let mut que = VecDeque::<usize>::new();
        for i in 0..self.api_functions.len() {
            if self.reserve[i] || !self.reachable[i] {
                continue;
            }
            let func = &self.api_functions[i];
            if let Some(ref output) = func.output {
                if any_type_match(diverse_types, output, &self.full_name_map, self.cache(), true) {
                    println!(
                        "[Diverse]{} is diverse",
                        self.api_functions[i]._pretty_print(self.cache())
                    );
                    self.reserve[i] = true;
                    que.push_back(i);
                }
            }
        }

        while let Some(id) = que.pop_front() {
            for input in self.api_functions[id].inputs.iter() {
                if diverse_types.get(input).is_some() {
                    continue;
                }

                diverse_types.insert(input.clone(), false);

                for i in 0..self.api_functions.len() {
                    if self.reserve[i] || !self.reachable[i] {
                        continue;
                    }
                    if let Some(ref output) = self.api_functions[i].output {
                        if api_util::_same_type(
                            output,
                            input,
                            true,
                            &self.full_name_map,
                            self.cache(),
                        )
                        .is_compatible()
                        {
                            self.reserve[i] = true;
                            *diverse_types.get_mut(input).unwrap() = true;
                            que.push_back(i);
                            println!(
                                "[Diverse]{} is diverse",
                                self.api_functions[i]._pretty_print(self.cache())
                            );
                        }
                    }
                }
            }
        }
    }

    pub fn search_reachable_solutions(&mut self, solvers: &mut Vec<GenericSolver>, type_trait_cache: &mut TypeTraitCache) {
        let mut num_iter = 0;
        loop {
            statistic::inc("ITERS");
            println!("=====Iteration #{}=====", num_iter);

            // Add reachable type to type candidates
            self.update_reachable_info();
            self.update_candidate_types();
            println!("===== Candidates =====");
            self.print_type_candidates();
            println!("===== !Candidates =====");

            let mut update = false;
            for i in 0..solvers.len() {
                // println!("iter={}, solve this:",num_iter);
                // solvers[i].current_function.pretty_print(&self.cx.cache);

                let last = solvers[i].num_solution();
                solvers[i].solve(&self.cx.cache, &mut self.trait_impl_map, type_trait_cache, &self.full_name_map);
                if last != solvers[i].num_solution() {
                    update = true;
                }
            }

            num_iter += 1;
            if !update {
                break;
            }
        }

        println!("===== all reachable func =====");
        for i in 0..self.api_functions.len() {
            if self.reachable[i] {
                println!("{}", self.api_functions[i]._pretty_print(self.cache()));
                if self.api_functions[i].is_local() {
                    statistic::inc("COVERED API");
                }
            }
        }
        println!("===== !all reachable func =====");
    }


    pub fn prune_by_diversity(&mut self, solvers: &mut Vec<GenericSolver>) {
        let mut diverse_types = FxHashMap::<Type, bool>::default();

        for solver in solvers.iter_mut() {
            solver.init_diverse_set(&mut diverse_types, self.cache());
        }

        print_diverse_types(&diverse_types);

        loop {
            self.update_reserve(&mut diverse_types);
            let mut update = false;
            statistic::inc("PRUNE_ITERS");
            println!("propagate start");
            for solver in solvers.iter_mut() {
                update |=
                    solver.propagate_reserve(&mut diverse_types, &self.full_name_map, self.cache());
            }
            print_diverse_types(&diverse_types);
            // early terminate
            if !update {
                break;
            }
        }

        /* for solver in solvers.iter_mut() {
            solver.reserve_least_one();
        } */
    }

    pub(crate) fn resolve_generic_functions(&mut self) {
        // init available struct
        let mut solvers = Vec::new();
        let num_function = self.generic_functions.len();
        let mut type_trait_cache = TypeTraitCache::new();
        self.trait_impl_map.init_concrete();

        // init solvers and do statistic
        for function in &self.api_functions {
            if function.is_local() {
                statistic::inc("API");
            }
        }

        for function in &self.generic_functions {
            if function.api_function.is_local() {
                statistic::inc("API");
                statistic::inc("GENERIC_API");
            }
        }

        for function in self.generic_functions.iter() {
            println!("[ApiGraph] Resolve this function");
            function.pretty_print(&self.cx.cache);
            solvers.push(GenericSolver::new(Rc::clone(&self.type_context), function.clone()));
        }

        // 1. find all reachable API
        self.search_reachable_solutions(&mut solvers, &mut type_trait_cache);
        // 2. reduce the number of API
        self.prune_by_diversity(&mut solvers);

        println!("unsolve generic function:");
        for i in 0..num_function {
            if !solvers[i].is_solvable() && self.generic_functions[i].api_function.is_local() {
                statistic::inc("UNSOLVABLE");
            }
            if solvers[i].num_solution() > 0 {
                if self.generic_functions[i].api_function.is_local() {
                    statistic::inc("COVERED API");
                    statistic::inc("COVERED GENERIC");
                }
            } else {
                if !solvers[i].is_solvable(){
                    print!("[unsolvable]");
                }
                self.generic_functions[i].pretty_print(&self.cx.cache);
            }
        }

        println!("all mono function:");
        let mut count = 0;
        for i in 0..num_function {
            if self.generic_functions[i].api_function.is_local() {
                statistic::add("MONO_FUNS", solvers[i].num_solution());
            }
            for (api_fun, is_reserved, impl_set) in solvers[i].take_solutions() {
                print!("",);
                count += 1;
                let reserve_tag = if is_reserved { "[R]" } else { "[ ]" };
                println!(
                    "{} monofun#{}:{} : {:?}",
                    reserve_tag,
                    count,
                    api_fun._pretty_print(self.cache()),
                    impl_set
                );
                if is_reserved {
                    if self.generic_functions[i].api_function.is_local() {
                        statistic::inc("RESERVE");
                    }
                    self.add_api_function(api_fun);
                }
            }
        }
    }

    pub(crate) fn add_api_function(&mut self, mut api_fun: ApiFunction) {
        if api_fun.contains_unsupported_fuzzable_type(&self.full_name_map, self.cache())
            || !api_fun.is_unsupported()
        {
            println!("{} contain unsupported fuzzable type", api_fun._pretty_print(self.cache()));
            // self.functions_with_unsupported_fuzzable_types.insert(api_fun.full_name.clone());
        } else {
            replace_lifetime(&mut api_fun);
            self.api_functions.push(api_fun);
        }
    }

    pub(crate) fn add_mod_visibility(&mut self, mod_name: &String, visibility: &Visibility) {
        self.mod_visibility.add_one_mod(mod_name, visibility);
    }

    pub(crate) fn filter_functions(&mut self) {
        // self.filter_functions_defined_on_prelude_type();
        self.filter_api_functions_by_mod_visibility();
    }

    /// functions of prelude type. These functions are not in current crate
    /// I
    /* pub(crate) fn filter_functions_defined_on_prelude_type(&mut self) {
        let prelude_types = prelude_type::get_all_preluded_type();
        if prelude_types.len() <= 0 {
            return;
        }
        self.api_functions = self
            .api_functions
            .drain(..)
            .filter(|api_function| api_function.is_defined_on_prelude_type(&prelude_types))
            .collect();
    } */

    pub(crate) fn filter_api_functions_by_mod_visibility(&mut self) {
        let invisible_mods = self.mod_visibility.get_invisible_mods();

        if invisible_mods.len() <= 0 {
            return;
        }

        let mut new_api_functions = Vec::new();
        for api_func in &self.api_functions {
            if !self.is_invisible_function(&api_func, &invisible_mods) {
                new_api_functions.push(api_func.clone());
            }
        }
        self.api_functions = new_api_functions;

        let mut new_generic_functions = Vec::new();
        for api_func in &self.generic_functions {
            if !self.is_invisible_function(&api_func.api_function, &invisible_mods) {
                new_generic_functions.push(api_func.clone());
            }
        }
        self.generic_functions = new_generic_functions;
    }

    pub(crate) fn is_invisible_function(
        &self,
        api_func: &ApiFunction,
        invisible_mods: &Vec<String>,
    ) -> bool {
        let api_func_name = &api_func.full_path;
        for invisible_mod in invisible_mods {
            if api_func_name.as_str().starts_with(invisible_mod.as_str()) {
                return true;
            }
            if let Some(ref trait_) = api_func.trait_ {
                if self
                    .get_full_path_from_def_id(trait_.def_id(self.cache()).unwrap())
                    .starts_with(invisible_mod)
                {
                    return true;
                }
            }
        }
        return false;
    }

    pub(crate) fn print_all_functions(&self) {
        println!("======= all functions =======");
        println!("num of normal functions: {}", self.api_functions.len());
        println!("num of generic functions: {}", self.generic_functions.len());
        let mut cnt = 0;
        let mut apis = 0;
        let mut generics = 0;
        for function in self.api_functions.iter() {
            let mark = if function.is_local() { "[L]" } else { "[ ]" };
            println!("{}#{}#{}", mark, cnt, function._pretty_print(self.cache()));
            cnt += 1;
            if function.is_local() {
                apis += 1;
            }
        }

        for function in self.generic_functions.iter() {
            let mark = if function.api_function.is_local() { "[L]" } else { "[ ]" };
            print!("{}#{}#", mark, cnt);
            cnt += 1;
            function.pretty_print(&self.cx.cache);
            if function.api_function.is_local() {
                apis += 1;
                generics += 1;
            }
        }
        println!("apis={}\ngenerics={}", apis, generics);
        println!("======= !all functions =======\n");
    }

    pub(crate) fn set_full_name_map(&mut self, full_name_map: &FullNameMap) {
        self.full_name_map = full_name_map.clone();
    }

    pub(crate) fn find_all_dependencies(&mut self) {
        //println!("find_dependencies");
        self.api_dependencies.clear();
        //两个api_function之间的dependency
        let api_num = self.api_functions.len();

        for i in 0..api_num {
            let first_fun = &self.api_functions[i];
            if first_fun._is_end_function(&self.full_name_map, self.cache()) {
                //如果第一个函数是终止节点，就不寻找这样的依赖
                continue;
            }
            if let Some(ty_) = &first_fun.output {
                let output_type = ty_;
                for j in 0..api_num {
                    //TODO:是否要把i=j的情况去掉？
                    let second_fun = &self.api_functions[j];
                    if second_fun._is_start_function(&self.full_name_map, self.cache()) {
                        //如果第二个节点是开始节点，那么直接跳过
                        continue;
                    }
                    let input_params = &second_fun.inputs;
                    let input_params_num = input_params.len();

                    for k in 0..input_params_num {
                        let input_param = &input_params[k];

                        let call_type = api_util::_same_type(
                            output_type,
                            input_param,
                            true,
                            &self.full_name_map,
                            self.cache(),
                        );
                        match &call_type {
                            CallType::_NotCompatible => {
                                continue;
                            }
                            _ => {
                                let one_dependency = ApiDependency {
                                    output_fun: (ApiType::BareFunction, i),
                                    input_fun: (ApiType::BareFunction, j),
                                    input_param_index: k,
                                    call_type: call_type.clone(),
                                };

                                self.api_dependencies.push(one_dependency);
                            }
                        }
                    }
                }
            }
        }
    }

    pub(crate) fn default_generate_sequences(&mut self) {
        //BFS + backward search
        self.generate_all_possoble_sequences(GraphTraverseAlgorithm::_BfsEndPoint);
        self._try_to_cover_unvisited_nodes();

        // backward search
        //self.generate_all_possoble_sequences(GraphTraverseAlgorithm::_DirectBackwardSearch);
    }

    pub(crate) fn generate_all_possoble_sequences(&mut self, algorithm: GraphTraverseAlgorithm) {
        //BFS序列的最大长度：即为函数的数量,或者自定义
        //let bfs_max_len = self.api_functions.len();
        let bfs_max_len = 3;
        //random walk的最大步数

        let random_walk_max_size = if RANDOM_WALK_STEPS.contains_key(self._crate_name.as_str()) {
            RANDOM_WALK_STEPS.get(self._crate_name.as_str()).unwrap().clone()
        } else {
            100000
        };

        //no depth bound
        let random_walk_max_depth = 0;
        //try deep sequence number
        let max_sequence_number = 100000;
        match algorithm {
            GraphTraverseAlgorithm::_Bfs => {
                println!("using bfs");
                self.bfs(bfs_max_len, false, false);
            }
            GraphTraverseAlgorithm::_FastBfs => {
                println!("using fastbfs");
                self.bfs(bfs_max_len, false, true);
            }
            GraphTraverseAlgorithm::_BfsEndPoint => {
                println!("using bfs end point");
                self.bfs(bfs_max_len, true, false);
            }
            GraphTraverseAlgorithm::_FastBfsEndPoint => {
                println!("using fast bfs end point");
                self.bfs(bfs_max_len, true, true);
            }
            GraphTraverseAlgorithm::_TryDeepBfs => {
                println!("using try deep bfs");
                self._try_deep_bfs(max_sequence_number);
            }
            GraphTraverseAlgorithm::_RandomWalk => {
                println!("using random walk");
                self.random_walk(random_walk_max_size, false, random_walk_max_depth);
            }
            GraphTraverseAlgorithm::_RandomWalkEndPoint => {
                println!("using random walk end point");
                self.random_walk(random_walk_max_size, true, random_walk_max_depth);
            }

            GraphTraverseAlgorithm::_DirectBackwardSearch => {
                println!("using backward search");
                self.api_sequences.clear();
                self.reset_visited();
                self._try_to_cover_unvisited_nodes();
            }
        }
    }

    pub(crate) fn reset_visited(&mut self) {
        self.api_functions_visited.clear();
        let api_function_num = self.api_functions.len();
        for _ in 0..api_function_num {
            self.api_functions_visited.push(false);
        }
        //TODO:还有别的序列可能需要reset
    }

    //检查是否所有函数都访问过了
    pub(crate) fn check_all_visited(&self) -> bool {
        let mut visited_nodes = 0;
        for visited in &self.api_functions_visited {
            if *visited {
                visited_nodes = visited_nodes + 1;
            }
        }

        if visited_nodes == self.api_functions_visited.len() {
            return true;
        } else {
            return false;
        }
    }

    //已经访问过的节点数量,用来快速判断bfs是否还需要run下去：如果一轮下来，bfs的长度没有发生变化，那么也可直接quit了
    pub(crate) fn _visited_nodes_num(&self) -> usize {
        let visited: Vec<&bool> =
            (&self.api_functions_visited).into_iter().filter(|x| **x == true).collect();
        visited.len()
    }

    //生成函数序列，且指定调用的参数
    //加入对fast mode的支持
    pub(crate) fn bfs(&mut self, max_len: usize, stop_at_end_function: bool, fast_mode: bool) {
        //清空所有的序列
        self.api_sequences.clear();
        self.reset_visited();
        if max_len < 1 {
            return;
        }

        let api_function_num = self.api_functions.len();

        //无需加入长度为1的，从空序列开始即可，加入一个长度为0的序列作为初始
        /* let api_sequence = ApiSequence::new();
        self.api_sequences.push(api_sequence); */

        let mut que = VecDeque::<ApiSequence>::new();
        que.push_back(ApiSequence::new());
        let mut nodes = FxHashSet::<usize>::default();
        //接下来开始从长度1一直到max_len遍历
        while let Some(seq) = que.pop_front() {
            if (!stop_at_end_function || !self.is_sequence_ended(&seq)) && seq.len() < max_len {
                let api_type = ApiType::BareFunction;
                for api_func_index in 0..api_function_num {
                    //bfs fast, 访问过的函数不再访问
                    if fast_mode && self.api_functions_visited[api_func_index] {
                        continue;
                    }
                    if let Some(new_sequence) =
                        self.is_fun_satisfied(&api_type, api_func_index, &seq)
                    {
                        nodes.insert(api_func_index);
                        que.push_back(new_sequence);
                        self.api_functions_visited[api_func_index] = true;
                        //bfs fast，如果都已经别访问过，直接退出
                        if self.check_all_visited() {
                            //println!("bfs all visited");
                            //return;
                        }
                    }
                }
            }
            self.api_sequences.push(seq);
        }
        let mut vec = nodes.into_iter().collect::<Vec<usize>>();
        vec.sort();
        for i in vec.iter() {
            print!("{}, ", *i);
        }
        print!("\n");
        //println!("There are total {} sequences after bfs", self.api_sequences.len());
        if !stop_at_end_function {
            std::process::exit(0);
        }
    }

    //为探索比较深的路径专门进行优化
    //主要还是针对比较大的库,函数比较多的
    pub(crate) fn _try_deep_bfs(&mut self, max_sequence_number: usize) {
        //清空所有的序列
        self.api_sequences.clear();
        self.reset_visited();
        let max_len = self.api_functions.len();
        if max_len < 1 {
            return;
        }

        let api_function_num = self.api_functions.len();

        //无需加入长度为1的，从空序列开始即可，加入一个长度为0的序列作为初始
        let api_sequence = ApiSequence::new();
        self.api_sequences.push(api_sequence);

        let mut already_covered_nodes = FxHashSet::default();
        let mut already_covered_edges = FxHashSet::default();
        //接下来开始从长度1一直到max_len遍历
        for len in 0..max_len {
            let current_sequence_number = self.api_sequences.len();
            let covered_nodes = self._visited_nodes_num();
            let mut has_new_coverage_flag = false;
            if len > 2 && current_sequence_number * covered_nodes >= max_sequence_number {
                break;
            }

            let mut tmp_sequences = Vec::new();
            for sequence in &self.api_sequences {
                if self.is_sequence_ended(sequence) {
                    //如果需要引入终止函数，并且当前序列的最后一个函数是终止函数，那么就不再继续添加
                    continue;
                }
                if sequence.len() == len {
                    tmp_sequences.push(sequence.clone());
                }
            }
            for sequence in &tmp_sequences {
                //长度为len的序列，去匹配每一个函数，如果可以加入的话，就生成一个新的序列
                let api_type = ApiType::BareFunction;
                for api_func_index in 0..api_function_num {
                    if let Some(new_sequence) =
                        self.is_fun_satisfied(&api_type, api_func_index, sequence)
                    {
                        let covered_nodes = new_sequence.get_contained_api_functions();
                        for covered_node in &covered_nodes {
                            if !already_covered_nodes.contains(covered_node) {
                                already_covered_nodes.insert(*covered_node);
                                has_new_coverage_flag = true;
                            }
                        }

                        let covered_edges = &new_sequence._covered_dependencies;
                        for covered_edge in covered_edges {
                            if !already_covered_edges.contains(covered_edge) {
                                already_covered_edges.insert(*covered_edge);
                                has_new_coverage_flag = true;
                            }
                        }

                        self.api_sequences.push(new_sequence);
                        self.api_functions_visited[api_func_index] = true;
                    }
                }
            }
            if !has_new_coverage_flag {
                println!("forward bfs can not find more.");
                break;
            }
        }
    }

    pub(crate) fn random_walk(
        &mut self,
        max_size: usize,
        stop_at_end_function: bool,
        max_depth: usize,
    ) {
        self.api_sequences.clear();
        self.reset_visited();

        //没有函数的话，直接return
        if self.api_functions.len() <= 0 {
            return;
        }

        //加入一个长度为0的序列
        let api_sequence = ApiSequence::new();
        self.api_sequences.push(api_sequence);

        //start random work
        let function_len = self.api_functions.len();
        let mut rng = rand::thread_rng();
        for i in 0..max_size {
            let current_sequence_len = self.api_sequences.len();
            let chosen_sequence_index = rng.gen_range(0, current_sequence_len);
            let chosen_sequence = &self.api_sequences[chosen_sequence_index];
            //如果需要在终止节点处停止
            if stop_at_end_function && self.is_sequence_ended(&chosen_sequence) {
                continue;
            }
            if max_depth > 0 && chosen_sequence.len() >= max_depth {
                continue;
            }
            let chosen_fun_index = rng.gen_range(0, function_len);
            //let chosen_fun = &self.api_functions[chosen_fun_index];
            let fun_type = ApiType::BareFunction;
            if let Some(new_sequence) =
                self.is_fun_satisfied(&fun_type, chosen_fun_index, chosen_sequence)
            {
                self.api_sequences.push(new_sequence);
                self.api_functions_visited[chosen_fun_index] = true;

                //如果全都已经访问过，直接退出
                if self.check_all_visited() {
                    println!("random run {} times", i);
                    //return;
                }
            }
        }
    }

    pub(crate) fn _choose_candidate_sequence_for_merge(&self) -> Vec<usize> {
        let mut res = Vec::new();
        let all_sequence_number = self.api_sequences.len();
        for i in 0..all_sequence_number {
            let api_sequence = &self.api_sequences[i];
            let dead_code = api_sequence._dead_code(self);
            let api_sequence_len = api_sequence.len();
            if self.is_sequence_ended(api_sequence) {
                //如果当前序列已经结束
                continue;
            }
            if api_sequence_len <= 0 {
                continue;
            } else if api_sequence_len == 1 {
                res.push(i);
            } else {
                let mut dead_code_flag = false;
                for j in 0..api_sequence_len - 1 {
                    if dead_code[j] {
                        dead_code_flag = true;
                        break;
                    }
                }
                if !dead_code_flag {
                    res.push(i);
                }
            }
        }
        res
    }

    pub(crate) fn _try_to_cover_unvisited_nodes(&mut self) {
        //println!("try to cover more nodes");
        let mut apis_covered_by_reverse_search = 0;
        let mut unvisited_nodes = FxHashSet::default();
        let api_fun_number = self.api_functions.len();
        for i in 0..api_fun_number {
            if !self.api_functions_visited[i] {
                unvisited_nodes.insert(i);
            }
        }
        let mut covered_node_this_iteration = FxHashSet::default();
        //最多循环没访问到的节点的数量
        for _ in 0..unvisited_nodes.len() {
            covered_node_this_iteration.clear();
            let candidate_sequences = self._choose_candidate_sequence_for_merge();
            //println!("sequence number, {}", self.api_sequences.len());
            //println!("candidate sequence number, {}", candidate_sequences.len());
            for unvisited_node in &unvisited_nodes {
                let unvisited_api_func = &self.api_functions[*unvisited_node];
                let inputs = &unvisited_api_func.inputs;
                let mut dependent_sequence_indexes = Vec::new();
                let mut can_be_covered_flag = true;
                let input_param_num = inputs.len();
                for i in 0..input_param_num {
                    let input_type = &inputs[i];
                    if api_util::is_fuzzable_type(input_type, &self.full_name_map, self.cache()) {
                        continue;
                    }
                    let mut can_find_dependency_flag = false;
                    let mut tmp_dependent_index = -1;
                    for candidate_sequence_index in &candidate_sequences {
                        let output_type = ApiType::BareFunction;
                        let input_type = ApiType::BareFunction;
                        let candidate_sequence = &self.api_sequences[*candidate_sequence_index];
                        let output_index = candidate_sequence.last_api_func_index().unwrap();

                        if let Some(_) = self.check_dependency(
                            &output_type,
                            output_index,
                            &input_type,
                            *unvisited_node,
                            i,
                        ) {
                            can_find_dependency_flag = true;
                            //dependent_sequence_indexes.push(*candidate_sequence_index);
                            tmp_dependent_index = *candidate_sequence_index as i32;

                            //prefer sequence with fuzzable inputs
                            if !candidate_sequence.has_no_fuzzables() {
                                break;
                            }
                        }
                    }
                    if !can_find_dependency_flag {
                        can_be_covered_flag = false;
                    } else {
                        dependent_sequence_indexes.push(tmp_dependent_index as usize);
                    }
                }
                if can_be_covered_flag {
                    //println!("{:?} can be covered", unvisited_api_func.full_name);
                    let dependent_sequences: Vec<ApiSequence> = dependent_sequence_indexes
                        .into_iter()
                        .map(|index| self.api_sequences[index].clone())
                        .collect();
                    let merged_sequence = ApiSequence::merge_sequences(&dependent_sequences);
                    let input_type = ApiType::BareFunction;
                    if let Some(generated_sequence) =
                        self.is_fun_satisfied(&input_type, *unvisited_node, &merged_sequence)
                    {
                        //println!("{}", generated_sequence._to_well_written_function(self, 0, 0));

                        self.api_sequences.push(generated_sequence);
                        self.api_functions_visited[*unvisited_node] = true;
                        covered_node_this_iteration.insert(*unvisited_node);
                        apis_covered_by_reverse_search = apis_covered_by_reverse_search + 1;
                    } else {
                        //The possible cause is there is some wrong fuzzable type
                        println!("Should not go to here. Only if algorithm error occurs");
                    }
                }
            }
            if covered_node_this_iteration.len() == 0 {
                println!("reverse search can not cover more nodes");
                break;
            } else {
                for covered_node in &covered_node_this_iteration {
                    unvisited_nodes.remove(covered_node);
                }
            }
        }

        let mut totol_sequences_number = 0;
        let mut total_length = 0;
        let mut covered_nodes = FxHashSet::default();
        let mut covered_edges = FxHashSet::default();

        for sequence in &self.api_sequences {
            if sequence.has_no_fuzzables() {
                continue;
            }
            totol_sequences_number = totol_sequences_number + 1;
            total_length = total_length + sequence.len();
            let cover_nodes = sequence.get_contained_api_functions();
            for cover_node in &cover_nodes {
                covered_nodes.insert(*cover_node);
            }

            let cover_edges = &sequence._covered_dependencies;
            for cover_edge in cover_edges {
                covered_edges.insert(*cover_edge);
            }
        }

        println!("after backward search");
        println!("targets = {}", totol_sequences_number);
        println!("total length = {}", total_length);
        let average_visit_time = (total_length as f64) / (covered_nodes.len() as f64);
        println!("average time to visit = {}", average_visit_time);
        println!("edge covered by reverse search = {}", covered_edges.len());

        //println!("There are total {} APIs covered by reverse search", apis_covered_by_reverse_search);
    }

    pub(crate) fn _naive_choose_sequence(&self, max_sequence_size: usize) -> Vec<ApiSequence> {
        let mut to_cover_nodes = Vec::new();
        let function_len = self.api_functions.len();
        for i in 0..function_len {
            if self.api_functions_visited[i] {
                to_cover_nodes.push(i);
            }
        }
        let to_cover_nodes_number = to_cover_nodes.len();
        println!("There are total {} nodes need to be covered.", to_cover_nodes_number);

        let mut chosen_sequence_flag = Vec::new();
        let prepared_sequence_number = self.api_sequences.len();
        for _ in 0..prepared_sequence_number {
            chosen_sequence_flag.push(false);
        }

        let mut res = Vec::new();
        let mut node_candidate_sequences = FxHashMap::default();

        for node in &to_cover_nodes {
            node_candidate_sequences.insert(*node, Vec::new());
        }

        for i in 0..prepared_sequence_number {
            let api_sequence = &self.api_sequences[i];
            let contains_nodes = api_sequence.get_contained_api_functions();
            for node in contains_nodes {
                if let Some(v) = node_candidate_sequences.get_mut(&node) {
                    if !v.contains(&i) {
                        v.push(i);
                    }
                }
            }
        }

        let mut rng = rand::thread_rng();
        for _ in 0..max_sequence_size {
            if to_cover_nodes.len() == 0 {
                println!("all {} nodes need to be covered is covered", to_cover_nodes_number);
                break;
            }
            //println!("need_to_cover_nodes:{:?}", to_cover_nodes);
            let next_cover_node = to_cover_nodes.first().unwrap();
            let candidate_sequences =
                node_candidate_sequences.get(next_cover_node).unwrap().clone();
            let unvisited_candidate_sequences = candidate_sequences
                .into_iter()
                .filter(|node| chosen_sequence_flag[*node] == false)
                .collect::<Vec<_>>();
            let candidate_number = unvisited_candidate_sequences.len();
            let random_index = rng.gen_range(0, candidate_number);
            let chosen_index = unvisited_candidate_sequences[random_index];
            //println!("randomc index{}", random_index);
            let chosen_sequence = &self.api_sequences[chosen_index];
            //println!("{:}",chosen_sequence._to_well_written_function(self, 0, 0));

            let covered_nodes = chosen_sequence.get_contained_api_functions();
            to_cover_nodes =
                to_cover_nodes.into_iter().filter(|node| !covered_nodes.contains(node)).collect();
            chosen_sequence_flag[random_index] = true;
            res.push(chosen_sequence.clone());
        }
        res
    }

    pub(crate) fn _random_choose(&self, max_size: usize) -> Vec<ApiSequence> {
        let mut res = Vec::new();
        let mut covered_nodes = FxHashSet::default();
        let mut covered_edges = FxHashSet::default();
        let mut sequence_indexes = Vec::new();

        let total_sequence_size = self.api_sequences.len();

        for i in 0..total_sequence_size {
            sequence_indexes.push(i);
        }

        let mut rng = rand::thread_rng();
        for _ in 0..max_size {
            let rest_sequences_number = sequence_indexes.len();
            if rest_sequences_number <= 0 {
                break;
            }

            let chosen_index = rng.gen_range(0, rest_sequences_number);
            let sequence_index = sequence_indexes[chosen_index];

            let sequence = &self.api_sequences[sequence_index];
            res.push(sequence.clone());
            sequence_indexes.remove(chosen_index);

            for covered_node in sequence.get_contained_api_functions() {
                covered_nodes.insert(covered_node);
            }

            for covered_edge in &sequence._covered_dependencies {
                covered_edges.insert(covered_edge.clone());
            }
        }

        println!("-----------STATISTICS-----------");
        println!("Random selection selected {} targets", res.len());
        println!("Random selection covered {} nodes", covered_nodes.len());
        println!("Random selection covered {} edges", covered_edges.len());
        println!("--------------------------------");

        res
    }

    pub(crate) fn _first_choose(&self, max_size: usize) -> Vec<ApiSequence> {
        let mut res = Vec::new();
        let mut covered_nodes = FxHashSet::default();
        let mut covered_edges = FxHashSet::default();

        let total_sequence_size = self.api_sequences.len();

        for index in 0..total_sequence_size {
            let sequence = &self.api_sequences[index];
            if sequence.has_no_fuzzables() {
                continue;
            }
            res.push(sequence.clone());

            for covered_node in sequence.get_contained_api_functions() {
                covered_nodes.insert(covered_node);
            }

            for covered_edge in &sequence._covered_dependencies {
                covered_edges.insert(covered_edge.clone());
            }

            if res.len() >= max_size {
                break;
            }
        }

        println!("-----------STATISTICS-----------");
        println!("Random walk selected {} targets", res.len());
        println!("Random walk covered {} nodes", covered_nodes.len());
        println!("Random walk covered {} edges", covered_edges.len());
        println!("--------------------------------");

        res
    }

    pub(crate) fn _heuristic_choose(
        &self,
        max_size: usize,
        stop_at_visit_all_nodes: bool,
    ) -> Vec<ApiSequence> {
        let mut res = Vec::new();
        let mut to_cover_nodes = Vec::new();

        let mut fixed_covered_nodes = FxHashSet::default();
        // println
        let mut num = 0;
        for fixed_sequence in &self.api_sequences {
            //let covered_nodes = fixed_sequence._get_contained_api_functions();
            //for covered_node in &covered_nodes {
            //    fixed_covered_nodes.insert(*covered_node);
            //}
            num += 1;
            if !fixed_sequence.has_no_fuzzables()
                && !fixed_sequence._contains_dead_code_except_last_one(self)
            {
                let covered_nodes = fixed_sequence.get_contained_api_functions();
                for covered_node in &covered_nodes {
                    fixed_covered_nodes.insert(*covered_node);
                }
            }
        }

        for fixed_covered_node in fixed_covered_nodes {
            to_cover_nodes.push(fixed_covered_node);
        }

        let to_cover_nodes_number = to_cover_nodes.len();
        println!("There are total {} nodes need to be covered.", to_cover_nodes_number);
        let to_cover_dependency_number = self.api_dependencies.len();
        println!("There are total {} edges need to be covered.", to_cover_dependency_number);
        let total_sequence_number = self.api_sequences.len();

        println!("There are toatl {} sequences.", total_sequence_number);
        let mut valid_fuzz_sequence_count = 0;
        for sequence in &self.api_sequences {
            if !sequence.has_no_fuzzables() && !sequence._contains_dead_code_except_last_one(self) {
                valid_fuzz_sequence_count = valid_fuzz_sequence_count + 1;
            }
        }
        println!("There are toatl {} valid sequences for fuzz.", valid_fuzz_sequence_count);
        if valid_fuzz_sequence_count <= 0 {
            return res;
        }

        //let mut already_covered_monos = FxHashSet::default();
        let mut already_covered_nodes = FxHashSet::default();
        let mut already_covered_edges = FxHashSet::default();
        let mut already_chosen_sequences = FxHashSet::default();
        let mut sorted_chosen_sequences = Vec::new();
        let mut dynamic_fuzzable_length_sequences_count = 0;
        let mut fixed_fuzzale_length_sequences_count = 0;

        let mut try_to_find_dynamic_length_flag = true;
        for _ in 0..max_size + 1 {
            let mut current_chosen_sequence_index = 0;
            let mut current_max_covered_nodes = 0;
            let mut current_max_covered_edges = 0;
            let mut current_chosen_sequence_len = 0;

            for j in 0..total_sequence_number {
                if already_chosen_sequences.contains(&j) {
                    continue;
                }
                let api_sequence = &self.api_sequences[j];

                if !api_sequence.has_mono() {
                    continue;
                }

                if api_sequence.has_no_fuzzables()
                {
                    // println!("Has no fuzzables {}", j);
                    continue;
                }

                if api_sequence._contains_dead_code_except_last_one(self){
                    // println!("contain dead code {}", j);
                    continue;
                }

                if try_to_find_dynamic_length_flag && api_sequence._is_fuzzables_fixed_length() {
                    //优先寻找fuzzable部分具有动态长度的情况
                    // println!("try_to_find_dynamic_length_flag1, {}",j);
                    continue;
                }

                if !try_to_find_dynamic_length_flag && !api_sequence._is_fuzzables_fixed_length() {
                    //再寻找fuzzable部分具有静态长度的情况
                    // println!("try_to_find_dynamic_length_flag2, {}",j);
                    continue;
                }

                let covered_nodes = api_sequence.get_contained_api_functions();
                let mut uncovered_nodes_by_former_sequence_count = 0;
                for covered_node in &covered_nodes {
                    if !already_covered_nodes.contains(covered_node) {
                        uncovered_nodes_by_former_sequence_count =
                            uncovered_nodes_by_former_sequence_count + 1;
                    }
                }

                if uncovered_nodes_by_former_sequence_count < current_max_covered_nodes {
                    // println!("smaller than max1, {}", j);
                    continue;
                }
                let covered_edges = &api_sequence._covered_dependencies;
                let mut uncovered_edges_by_former_sequence_count = 0;
                for covered_edge in covered_edges {
                    if !already_covered_edges.contains(covered_edge) {
                        uncovered_edges_by_former_sequence_count =
                            uncovered_edges_by_former_sequence_count + 1;
                    }
                }
                if uncovered_nodes_by_former_sequence_count == current_max_covered_nodes
                    && uncovered_edges_by_former_sequence_count < current_max_covered_edges
                {
                    // println!("smaller than max2, {}",j);
                    continue;
                }
                let sequence_len = api_sequence.len();
                if (uncovered_nodes_by_former_sequence_count > current_max_covered_nodes)
                    || (uncovered_nodes_by_former_sequence_count == current_max_covered_nodes
                        && uncovered_edges_by_former_sequence_count > current_max_covered_edges)
                    || (uncovered_nodes_by_former_sequence_count == current_max_covered_nodes
                        && uncovered_edges_by_former_sequence_count == current_max_covered_edges
                        && sequence_len < current_chosen_sequence_len)
                {
                    current_chosen_sequence_index = j;
                    current_max_covered_nodes = uncovered_nodes_by_former_sequence_count;
                    current_max_covered_edges = uncovered_edges_by_former_sequence_count;
                    current_chosen_sequence_len = sequence_len;
                }
            }

            if try_to_find_dynamic_length_flag && current_max_covered_nodes <= 0 {
                println!("sequences with dynamic length can not cover more nodes");
                try_to_find_dynamic_length_flag = false;
                continue;
            }

            if !try_to_find_dynamic_length_flag
                && current_max_covered_edges <= 0
                && current_max_covered_nodes <= 0
            {
                println!("can't cover more edges or nodes");
                break;
            }
            already_chosen_sequences.insert(current_chosen_sequence_index);
            sorted_chosen_sequences.push(current_chosen_sequence_index);

            if try_to_find_dynamic_length_flag {
                dynamic_fuzzable_length_sequences_count =
                    dynamic_fuzzable_length_sequences_count + 1;
            } else {
                fixed_fuzzale_length_sequences_count = fixed_fuzzale_length_sequences_count + 1;
            }

            let chosen_sequence = &self.api_sequences[current_chosen_sequence_index];

            /* let cover_monos=chosen_sequence.get_mono_nodes_no();
            for mono_no in cover_monos {
                already_covered_monos.insert(mono_no);
            } */

            let covered_nodes = chosen_sequence.get_contained_api_functions();
            for cover_node in covered_nodes {
                already_covered_nodes.insert(cover_node);
            }
            let covered_edges = &chosen_sequence._covered_dependencies;
            //println!("covered_edges = {:?}", covered_edges);
            for cover_edge in covered_edges {
                already_covered_edges.insert(*cover_edge);
            }

            if already_chosen_sequences.len() == valid_fuzz_sequence_count {
                //println!("all sequence visited");
                break;
            }
            if to_cover_dependency_number != 0
                && already_covered_edges.len() == to_cover_dependency_number
            {
                //println!("all edges visited");
                //should we stop at visit all edges?
                break;
            }
            if stop_at_visit_all_nodes && already_covered_nodes.len() == to_cover_nodes_number {
                //println!("all nodes visited");
                break;
            }
            //println!("no fuzzable count = {}", no_fuzzable_count);
        }

        let total_functions_number = self.api_functions.len();
        println!("-----------STATISTICS-----------");
        println!("total nodes: {}", total_functions_number);

        let mut valid_api_number = 0;
        for api_function_ in &self.api_functions {
            if !api_function_.contains_unsupported_fuzzable_type(&self.full_name_map, self.cache())
            {
                valid_api_number = valid_api_number + 1;
            }
        }
        //println!("total valid nodes: {}", valid_api_number);

        let total_dependencies_number = self.api_dependencies.len();
        println!("total edges: {}", total_dependencies_number);

        let covered_node_num = already_covered_nodes.len();
        println!("covered nodes: {}", covered_node_num);

        let mut covered_mono_num = 0;
        for no in already_covered_nodes.iter() {
            if self.api_functions[*no].is_mono() {
                covered_mono_num += 1;
                print!("{}, ", *no)
            }
        }
        print!("\n");
        println!("covered monos: {}", covered_mono_num);

        let covered_edges_num = already_covered_edges.len();
        println!("covered edges: {}", covered_edges_num);

        let node_coverage = (already_covered_nodes.len() as f64) / (valid_api_number as f64);
        let edge_coverage =
            (already_covered_edges.len() as f64) / (total_dependencies_number as f64);
        println!("node coverage: {}", node_coverage);
        println!("edge coverage: {}", edge_coverage);
        //println!("sequence with dynamic fuzzable length: {}", dynamic_fuzzable_length_sequences_count);
        //println!("sequence with fixed fuzzable length: {}",fixed_fuzzale_length_sequences_count);

        let mut sequnce_covered_by_reverse_search = 0;
        let mut max_length = 0;
        for sequence_index in sorted_chosen_sequences {
            let api_sequence = self.api_sequences[sequence_index].clone();

            if api_sequence.len() > 3 {
                sequnce_covered_by_reverse_search = sequnce_covered_by_reverse_search + 1;
                if api_sequence.len() > max_length {
                    max_length = api_sequence.len();
                }
            }

            res.push(api_sequence);
        }

        println!("targets covered by reverse search: {}", sequnce_covered_by_reverse_search);
        println!("total targets: {}", res.len());
        println!("max length = {}", max_length);

        let mut total_length = 0;
        for selected_sequence in &res {
            total_length = total_length + selected_sequence.len();
        }

        println!("total length = {}", total_length);
        let average_time_to_fuzz_each_api =
            (total_length as f64) / (already_covered_nodes.len() as f64);
        println!("average time to fuzz each api = {}", average_time_to_fuzz_each_api);

        println!("--------------------------------");

        res
    }

    //判断一个函数能否加入给定的序列中,如果可以加入，返回Some(new_sequence),new_sequence是将新的调用加进去之后的情况，否则返回None
    pub(crate) fn is_fun_satisfied(
        &self,
        input_type: &ApiType,
        input_fun_index: usize,
        sequence: &ApiSequence,
    ) -> Option<ApiSequence> {
        //判断一个给定的函数能否加入到一个sequence中去
        match input_type {
            ApiType::BareFunction => {
                let mut new_sequence = sequence.clone();
                let mut api_call = ApiCall::_new(input_fun_index);
                let mut _moved_indexes = FxHashSet::default(); //用来保存发生move的那些语句的index
                //用来保存会被多次可变引用的情况
                let mut _multi_mut = FxHashSet::default();
                let mut _immutable_borrow = FxHashSet::default();

                let input_function = &self.api_functions[input_fun_index];
                let is_mono = input_function.is_mono();
                //如果是个unsafe函数，给sequence添加unsafe标记
                if input_function._unsafe_tag._is_unsafe() {
                    new_sequence.set_unsafe();
                }
                if let Some(ref trait_) = input_function.trait_ {
                    new_sequence.add_trait(trait_.def_id(self.cache()).unwrap());
                }

                let input_params = &input_function.inputs;
                let input_params_num = input_params.len();
                if input_params_num == 0 {
                    //无需输入参数，直接是可满足的
                    new_sequence.add_fn(api_call, is_mono);
                    return Some(new_sequence);
                }

                for i in 0..input_params_num {
                    let current_ty = &input_params[i];
                    let fuzzable_call_type = fuzzable_type::fuzzable_call_type(
                        current_ty,
                        &self.full_name_map,
                        self.cache(),
                    );
                    //如果当前参数是fuzzable的
                    if fuzzable_call_type.is_fuzzable() {
                        let current_fuzzable_index = new_sequence.fuzzable_params.len();
                        let (fuzzable_type, call_type) =
                            fuzzable_call_type.generate_fuzzable_type_and_call_type();
                        //如果出现了下面这段话，说明出现了Fuzzable参数但不知道如何参数化的
                        //典型例子是tuple里面出现了引用（&usize），这种情况不再去寻找dependency，直接返回无法添加即可
                        match &fuzzable_type {
                            FuzzableType::NoFuzzable => {
                                //println!("Fuzzable Type Error Occurs!");
                                //println!("type = {:?}", current_ty);
                                //println!("fuzzable_call_type = {:?}", fuzzable_call_type);
                                //println!("fuzzable_type = {:?}", fuzzable_type);
                                return None;
                            }
                            FuzzableType::Primitive(PrimitiveType::Str) => {
                                unreachable!("raw str! => {}, {:?}", input_fun_index, current_ty);
                            }
                            _ => {}
                        }

                        //判断要不要加mut tag
                        if api_util::_need_mut_tag(&call_type) {
                            new_sequence._insert_fuzzable_mut_tag(current_fuzzable_index);
                        }

                        //添加到sequence中去
                        new_sequence.fuzzable_params.push(fuzzable_type);
                        api_call._add_param(
                            ParamType::_FuzzableType,
                            current_fuzzable_index,
                            call_type,
                        );
                        continue;
                    }
                    //如果当前参数不是fuzzable的，那么就去api sequence寻找是否有这个依赖
                    //TODO:处理move的情况
                    let functions_in_sequence_len = sequence.functions.len();
                    let mut dependency_flag = false;

                    for function_index in 0..functions_in_sequence_len {
                        //如果这个sequence里面的该函数返回值已经被move掉了，那么就跳过，不再能被使用了
                        if new_sequence.is_moved(function_index)
                            || _moved_indexes.contains(&function_index)
                        {
                            continue;
                        }
                        let found_function = &new_sequence.functions[function_index];
                        let (api_type, index) = &found_function.func;
                        if let Some(dependency_index) =
                            self.check_dependency(api_type, *index, input_type, input_fun_index, i)
                        {
                            let dependency_ = self.api_dependencies[dependency_index].clone();
                            //将覆盖到的边加入到新的sequence中去
                            new_sequence.add_dependency(dependency_index);
                            //找到了依赖，当前参数是可以被满足的，设置flag并退出循环
                            dependency_flag = true;
                            //如果满足move发生的条件，那么
                            if api_util::_move_condition(current_ty, &dependency_.call_type) {
                                if _multi_mut.contains(&function_index)
                                    || _immutable_borrow.contains(&function_index)
                                {
                                    dependency_flag = false;
                                    continue;
                                } else {
                                    _moved_indexes.insert(function_index);
                                }
                            }
                            //如果当前调用是可变借用
                            if api_util::_is_mutable_borrow_occurs(
                                current_ty,
                                &dependency_.call_type,
                            ) {
                                //如果之前已经被借用过了
                                if _multi_mut.contains(&function_index)
                                    || _immutable_borrow.contains(&function_index)
                                {
                                    dependency_flag = false;
                                    continue;
                                } else {
                                    _multi_mut.insert(function_index);
                                }
                            }
                            //如果当前调用是引用，且之前已经被可变引用过，那么这个引用是非法的
                            if api_util::_is_immutable_borrow_occurs(
                                current_ty,
                                &dependency_.call_type,
                            ) {
                                if _multi_mut.contains(&function_index) {
                                    dependency_flag = false;
                                    continue;
                                } else {
                                    _immutable_borrow.insert(function_index);
                                }
                            }
                            //参数需要加mut 标记的话
                            if api_util::_need_mut_tag(&dependency_.call_type) {
                                new_sequence._insert_function_mut_tag(function_index);
                            }
                            //如果call type是unsafe的，那么给sequence加上unsafe标记
                            if dependency_.call_type.unsafe_call_type()._is_unsafe() {
                                new_sequence.set_unsafe();
                            }
                            api_call._add_param(
                                ParamType::_FunctionReturn,
                                function_index,
                                dependency_.call_type,
                            );
                            break;
                        }
                    }
                    if !dependency_flag {
                        //如果这个参数没有寻找到依赖，则这个函数不可以被加入到序列中
                        return None;
                    }
                }
                //所有参数都可以找到依赖，那么这个函数就可以加入序列
                new_sequence.add_fn(api_call, is_mono);
                for move_index in _moved_indexes {
                    new_sequence.insert_move_index(move_index);
                }
                if new_sequence._contains_multi_dynamic_length_fuzzable() {
                    //如果新生成的序列包含多维可变的参数，就不把这个序列加进去
                    // println!("func {} fail by Dynamic", input_fun_index);
                    return None;
                }
                return Some(new_sequence);
            }
        }
    }

    //判断一个依赖是否存在,存在的话返回Some(ApiDependency),否则返回None
    pub(crate) fn check_dependency(
        &self,
        output_type: &ApiType,
        output_index: usize,
        input_type: &ApiType,
        input_index: usize,
        input_param_index_: usize,
    ) -> Option<usize> {
        let dependency_num = self.api_dependencies.len();
        for index in 0..dependency_num {
            let dependency = &self.api_dependencies[index];
            //TODO:直接比较每一项内容是否可以节省点时间？
            let tmp_dependency = ApiDependency {
                output_fun: (*output_type, output_index),
                input_fun: (*input_type, input_index),
                input_param_index: input_param_index_,
                call_type: dependency.call_type.clone(),
            };
            if tmp_dependency == *dependency {
                //存在依赖
                return Some(index);
            }
        }
        //没找到依赖
        return None;
    }

    //判断一个调用序列是否已经到达终止端点
    fn is_sequence_ended(&self, api_sequence: &ApiSequence) -> bool {
        let functions = &api_sequence.functions;
        let last_fun = functions.last();
        let cache = self.cache();
        match last_fun {
            None => false,
            Some(api_call) => {
                let (api_type, index) = &api_call.func;
                match api_type {
                    _ => {
                        let last_func = &self.api_functions[*index];
                        if last_func._is_end_function(&self.full_name_map, cache) {
                            return true;
                        } else {
                            return false;
                        }
                    }
                }
            }
        }
    }
}
