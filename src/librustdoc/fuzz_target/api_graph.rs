use crate::formats::cache::Cache;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_sequence::{ApiCall, ApiSequence, ParamType};
use crate::fuzz_target::api_util;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzz_target_renderer::FuzzTargetContext;
use crate::fuzz_target::fuzzable_type;
use crate::fuzz_target::fuzzable_type::FuzzableType;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::mod_visibility::ModVisibity;
use crate::fuzz_target::prelude_type;
use crate::TyCtxt;
use lazy_static::lazy_static;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::rc::Rc;
use std::fmt;
//use crate::clean::{PrimitiveType};
use rand::{self, Rng};

use crate::clean::Visibility;

use super::generic_function::GenericFunction;

lazy_static! {
    static ref RANDOM_WALK_STEPS: FxHashMap<&'static str, usize> = {
        let mut m = FxHashMap::default();
        m.insert("regex", 10000);
        m.insert("url", 10000);
        m.insert("time", 10000);
        m
    };
}

lazy_static! {
    static ref CAN_COVER_NODES: FxHashMap<&'static str, usize> = {
        let mut m = FxHashMap::default();
        m.insert("regex", 96);
        m.insert("serde_json", 41);
        m.insert("clap", 66);
        m
    };
}

#[derive(Clone)]
pub(crate) struct ApiGraph<'tcx> {
    pub(crate) _crate_name: String,
    pub(crate) api_functions: Vec<ApiFunction>,
    pub(crate) api_functions_visited: Vec<bool>,
    pub(crate) api_dependencies: Vec<ApiDependency>,
    pub(crate) api_sequences: Vec<ApiSequence>,
    pub(crate) full_name_map: FullNameMap,  //did to full_name
    pub(crate) mod_visibility: ModVisibity, //the visibility of mods，to fix the problem of `pub(crate) use`
    pub(crate) generic_functions: Vec<GenericFunction>,
    pub(crate) functions_with_unsupported_fuzzable_types: FxHashSet<String>,
    pub(crate) cx: Rc<FuzzTargetContext<'tcx>>, //pub(crate) _sequences_of_all_algorithm : FxHashMap<GraphTraverseAlgorithm, Vec<ApiSequence>>
}

/* impl fmt::Debug for ApiGraph{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>{
        f.debug_struct("ApiGraph").field("api_functions",&self.api_functions).field("api_functions_visited",self.api_functions_visited)
        Ok(())
    }
} */

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
    //GenericFunction, currently not support now
}

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
        //let _sequences_of_all_algorithm = FxHashMap::default();
        ApiGraph {
            api_functions: Vec::new(),
            api_functions_visited: Vec::new(),
            api_dependencies: Vec::new(),
            api_sequences: Vec::new(),
            full_name_map: FullNameMap::new(),
            mod_visibility: ModVisibity::new(&_crate_name),
            generic_functions: Vec::new(),
            functions_with_unsupported_fuzzable_types: FxHashSet::default(),
            _crate_name,
            cx,
        }
    }

    pub(crate) fn cache(&self) -> &Cache {
        &self.cx.cache
    }

    pub(crate) fn tcx(&self) -> TyCtxt<'tcx> {
        self.cx.tcx
    }

    pub(crate) fn add_api_function(&mut self, api_fun: ApiFunction) {
        if api_fun._is_generic_function() {
            let generic_function = GenericFunction::from(api_fun);
            self.generic_functions.push(generic_function);
        } else if api_fun.contains_unsupported_fuzzable_type(&self.full_name_map, self.cache()) {
            self.functions_with_unsupported_fuzzable_types.insert(api_fun.full_name.clone());
        } else {
            self.api_functions.push(api_fun);
        }
    }

    pub(crate) fn add_mod_visibility(&mut self, mod_name: &String, visibility: &Visibility) {
        self.mod_visibility.add_one_mod(mod_name, visibility);
    }

    pub(crate) fn filter_functions(&mut self) {
        self.filter_functions_defined_on_prelude_type();
        self.filter_api_functions_by_mod_visibility();
    }

    /// functions of prelude type. These functions are not in current crate
    /// I
    pub(crate) fn filter_functions_defined_on_prelude_type(&mut self) {
        let prelude_types = prelude_type::get_all_preluded_type();
        if prelude_types.len() <= 0 {
            return;
        }
        self.api_functions = self
            .api_functions
            .drain(..)
            .filter(|api_function| api_function.is_defined_on_prelude_type(&prelude_types))
            .collect();
    }

    pub(crate) fn filter_api_functions_by_mod_visibility(&mut self) {
        let invisible_mods = self.mod_visibility.get_invisible_mods();

        if invisible_mods.len() <= 0 {
            return;
        }

        let mut new_api_functions = Vec::new();
        for api_func in &self.api_functions {
            let api_func_name = &api_func.full_name;
            let trait_name = &api_func._trait_full_path;
            let mut invisible_flag = false;
            for invisible_mod in &invisible_mods {
                if api_func_name.as_str().starts_with(invisible_mod.as_str()) {
                    invisible_flag = true;
                    break;
                }
                if let Some(trait_name_) = trait_name {
                    if trait_name_.as_str().starts_with(invisible_mod) {
                        invisible_flag = true;
                        break;
                    }
                }
            }
            if !invisible_flag {
                new_api_functions.push(api_func.clone());
            }
        }
        self.api_functions = new_api_functions;
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

        if CAN_COVER_NODES.contains_key(self._crate_name.as_str()) {
            let to_cover_nodes = CAN_COVER_NODES.get(self._crate_name.as_str()).unwrap().clone();
            if visited_nodes == to_cover_nodes {
                return true;
            } else {
                return false;
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
        let api_sequence = ApiSequence::new();
        self.api_sequences.push(api_sequence);

        //接下来开始从长度1一直到max_len遍历
        for len in 0..max_len {
            let mut tmp_sequences = Vec::new();
            for sequence in &self.api_sequences {
                if stop_at_end_function && self.is_sequence_ended(sequence) {
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
                    //bfs fast, 访问过的函数不再访问
                    if fast_mode && self.api_functions_visited[api_func_index] {
                        continue;
                    }
                    if let Some(new_sequence) =
                        self.is_fun_satisfied(&api_type, api_func_index, sequence)
                    {
                        self.api_sequences.push(new_sequence);
                        self.api_functions_visited[api_func_index] = true;

                        //bfs fast，如果都已经别访问过，直接退出
                        if self.check_all_visited() {
                            //println!("bfs all visited");
                            //return;
                        }
                    }
                }
            }
        }

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
                        let covered_nodes = new_sequence._get_contained_api_functions();
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
                        let output_index = candidate_sequence._last_api_func_index().unwrap();

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
                            if !candidate_sequence._has_no_fuzzables() {
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
                    let merged_sequence = ApiSequence::_merge_sequences(&dependent_sequences);
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
            if sequence._has_no_fuzzables() {
                continue;
            }
            totol_sequences_number = totol_sequences_number + 1;
            total_length = total_length + sequence.len();
            let cover_nodes = sequence._get_contained_api_functions();
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
            let contains_nodes = api_sequence._get_contained_api_functions();
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

            let covered_nodes = chosen_sequence._get_contained_api_functions();
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

            for covered_node in sequence._get_contained_api_functions() {
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
            if sequence._has_no_fuzzables() {
                continue;
            }
            res.push(sequence.clone());

            for covered_node in sequence._get_contained_api_functions() {
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
        for fixed_sequence in &self.api_sequences {
            //let covered_nodes = fixed_sequence._get_contained_api_functions();
            //for covered_node in &covered_nodes {
            //    fixed_covered_nodes.insert(*covered_node);
            //}

            if !fixed_sequence._has_no_fuzzables()
                && !fixed_sequence._contains_dead_code_except_last_one(self)
            {
                let covered_nodes = fixed_sequence._get_contained_api_functions();
                for covered_node in &covered_nodes {
                    fixed_covered_nodes.insert(*covered_node);
                }
            }
        }

        for fixed_covered_node in fixed_covered_nodes {
            to_cover_nodes.push(fixed_covered_node);
        }

        let to_cover_nodes_number = to_cover_nodes.len();
        //println!("There are total {} nodes need to be covered.", to_cover_nodes_number);
        let to_cover_dependency_number = self.api_dependencies.len();
        //println!("There are total {} edges need to be covered.", to_cover_dependency_number);
        let total_sequence_number = self.api_sequences.len();

        //println!("There are toatl {} sequences.", total_sequence_number);
        let mut valid_fuzz_sequence_count = 0;
        for sequence in &self.api_sequences {
            if !sequence._has_no_fuzzables() && !sequence._contains_dead_code_except_last_one(self)
            {
                valid_fuzz_sequence_count = valid_fuzz_sequence_count + 1;
            }
        }
        //println!("There are toatl {} valid sequences for fuzz.", valid_fuzz_sequence_count);
        if valid_fuzz_sequence_count <= 0 {
            return res;
        }

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

                if api_sequence._has_no_fuzzables()
                    || api_sequence._contains_dead_code_except_last_one(self)
                {
                    continue;
                }

                if try_to_find_dynamic_length_flag && api_sequence._is_fuzzables_fixed_length() {
                    //优先寻找fuzzable部分具有动态长度的情况
                    continue;
                }

                if !try_to_find_dynamic_length_flag && !api_sequence._is_fuzzables_fixed_length() {
                    //再寻找fuzzable部分具有静态长度的情况
                    continue;
                }

                let covered_nodes = api_sequence._get_contained_api_functions();
                let mut uncovered_nodes_by_former_sequence_count = 0;
                for covered_node in &covered_nodes {
                    if !already_covered_nodes.contains(covered_node) {
                        uncovered_nodes_by_former_sequence_count =
                            uncovered_nodes_by_former_sequence_count + 1;
                    }
                }

                if uncovered_nodes_by_former_sequence_count < current_max_covered_nodes {
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
                //println!("sequences with dynamic length can not cover more nodes");
                try_to_find_dynamic_length_flag = false;
                continue;
            }

            if !try_to_find_dynamic_length_flag
                && current_max_covered_edges <= 0
                && current_max_covered_nodes <= 0
            {
                //println!("can't cover more edges or nodes");
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

            let covered_nodes = chosen_sequence._get_contained_api_functions();
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
            } //else {
              //    println!("{}", api_function_._pretty_print(&self.full_name_map));
              //}
        }
        //println!("total valid nodes: {}", valid_api_number);

        let total_dependencies_number = self.api_dependencies.len();
        println!("total edges: {}", total_dependencies_number);

        let covered_node_num = already_covered_nodes.len();
        let covered_edges_num = already_covered_edges.len();
        println!("covered nodes: {}", covered_node_num);
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
                //如果是个unsafe函数，给sequence添加unsafe标记
                if input_function._unsafe_tag._is_unsafe() {
                    new_sequence.set_unsafe();
                }
                if input_function._trait_full_path.is_some() {
                    let trait_full_path = input_function._trait_full_path.as_ref().unwrap();
                    new_sequence.add_trait(trait_full_path);
                }
                let input_params = &input_function.inputs;
                let input_params_num = input_params.len();
                if input_params_num == 0 {
                    //无需输入参数，直接是可满足的
                    new_sequence._add_fn(api_call);
                    return Some(new_sequence);
                }

                for i in 0..input_params_num {
                    let current_ty = &input_params[i];
                    if api_util::is_fuzzable_type(current_ty, &self.full_name_map, self.cache()) {
                        //如果当前参数是fuzzable的
                        let current_fuzzable_index = new_sequence.fuzzable_params.len();
                        let fuzzable_call_type = fuzzable_type::fuzzable_call_type(
                            current_ty,
                            &self.full_name_map,
                            self.cache(),
                        );
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
                        if new_sequence._is_moved(function_index)
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
                            new_sequence._add_dependency(dependency_index);
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
                new_sequence._add_fn(api_call);
                for move_index in _moved_indexes {
                    new_sequence._insert_move_index(move_index);
                }
                if new_sequence._contains_multi_dynamic_length_fuzzable() {
                    //如果新生成的序列包含多维可变的参数，就不把这个序列加进去
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
                    ApiType::BareFunction => {
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
