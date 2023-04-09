use crate::formats::cache::Cache;
use crate::fuzz_target::afl_util::{self, _AflHelpers};
use crate::fuzz_target::api_graph::{ApiGraph, ApiType};
use crate::fuzz_target::api_util;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzzable_type::FuzzableType;
use crate::fuzz_target::prelude_type;
use crate::fuzz_target::replay_util;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub(crate) enum ParamType {
    _FunctionReturn,
    _FuzzableType,
}
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub(crate) struct ApiCall {
    pub(crate) func: (ApiType, usize), //要调用的函数类型，以及在对应数组中的位置
    pub(crate) params: Vec<(ParamType, usize, CallType)>, //参数类型(表示是使用之前的返回值，还是使用fuzzable的变量)，在当前的调用序列中参数所在的位置，以及如何调用
}

impl ApiCall {
    pub(crate) fn _new_without_params(api_type: &ApiType, index: usize) -> Self {
        let func = (api_type.clone(), index);
        let params = Vec::new();
        ApiCall { func, params }
    }

    pub(crate) fn _new(fun_index: usize) -> Self {
        let api_type = ApiType::BareFunction;
        let func = (api_type, fun_index);
        let params = Vec::new();
        ApiCall { func, params }
    }

    pub(crate) fn _add_param(
        &mut self,
        param_type: ParamType,
        param_index: usize,
        call_type: CallType,
    ) {
        self.params.push((param_type, param_index, call_type));
    }
}

//function call sequences
#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct ApiSequence {
    //TODO:如何表示函数调用序列？
    pub(crate) functions: Vec<ApiCall>,             //函数调用序列
    pub(crate) fuzzable_params: Vec<FuzzableType>,  //需要传入的fuzzable变量
    pub(crate) _using_traits: Vec<String>,          //需要use引入的traits的路径
    pub(crate) _unsafe_tag: bool,                   //标志这个调用序列是否需要加上unsafe标记
    pub(crate) _moved: FxHashSet<usize>,            //表示哪些返回值已经被move掉，不再能被使用
    pub(crate) _fuzzable_mut_tag: FxHashSet<usize>, //表示哪些fuzzable的变量需要带上mut标记
    pub(crate) _function_mut_tag: FxHashSet<usize>, //表示哪些function的返回值需要带上mut标记
    pub(crate) _covered_dependencies: FxHashSet<usize>, //表示用到了哪些dependency,即边覆盖率
}

impl ApiSequence {
    pub(crate) fn new() -> Self {
        let functions = Vec::new();
        let fuzzable_params = Vec::new();
        let _using_traits = Vec::new();
        let _unsafe_tag = false;
        let _moved = FxHashSet::default();
        let _fuzzable_mut_tag = FxHashSet::default();
        let _function_mut_tag = FxHashSet::default();
        let _covered_dependencies = FxHashSet::default();
        ApiSequence {
            functions,
            fuzzable_params,
            _using_traits,
            _unsafe_tag,
            _moved,
            _fuzzable_mut_tag,
            _function_mut_tag,
            _covered_dependencies,
        }
    }

    pub(crate) fn _add_fn_without_params(&mut self, api_type: &ApiType, index: usize) {
        let api_call = ApiCall::_new_without_params(api_type, index);
        self.functions.push(api_call);
    }

    pub(crate) fn _add_dependency(&mut self, dependency: usize) {
        self._covered_dependencies.insert(dependency);
    }

    pub(crate) fn len(&self) -> usize {
        self.functions.len()
    }

    pub(crate) fn _has_no_fuzzables(&self) -> bool {
        if self.fuzzable_params.len() <= 0 {
            return true;
        } else {
            return false;
        }
    }

    pub(crate) fn _last_api_func_index(&self) -> Option<usize> {
        if self.len() == 0 {
            None
        } else {
            let last_api_call = self.functions.last().unwrap();
            let (api_type, index) = &last_api_call.func;
            match api_type {
                ApiType::BareFunction => Some(*index),
            }
        }
    }

    pub(crate) fn _merge_another_sequence(&self, other: &ApiSequence) -> Self {
        let mut res = self.clone();
        let first_func_number = res.functions.len();
        let first_fuzzable_number = res.fuzzable_params.len();
        let mut other_sequence = other.clone();
        //functions
        for other_function in &other_sequence.functions {
            let other_func = other_function.func.clone();
            let mut new_other_params = Vec::new();
            for (param_type, index, call_type) in &other_function.params {
                let new_index = match param_type {
                    ParamType::_FuzzableType => *index + first_fuzzable_number,
                    ParamType::_FunctionReturn => *index + first_func_number,
                };
                new_other_params.push((param_type.clone(), new_index, call_type.clone()));
            }
            let new_other_function = ApiCall { func: other_func, params: new_other_params };
            res.functions.push(new_other_function);
        }
        //fuzzable_params
        res.fuzzable_params.append(&mut other_sequence.fuzzable_params);
        //using_trait
        res._using_traits.append(&mut other_sequence._using_traits);
        //unsafe tag
        res._unsafe_tag =
            if other_sequence._unsafe_tag { other_sequence._unsafe_tag } else { res._unsafe_tag };
        //move tag
        for move_tag in other_sequence._moved {
            res._moved.insert(move_tag + first_func_number);
        }
        //fuzzable mut tag
        for fuzzable_mut_tag in other_sequence._fuzzable_mut_tag {
            res._fuzzable_mut_tag.insert(fuzzable_mut_tag + first_fuzzable_number);
        }
        //function mut tag
        for function_mut_tag in other_sequence._function_mut_tag {
            res._function_mut_tag.insert(function_mut_tag + first_func_number);
        }
        res
    }

    pub(crate) fn _merge_sequences(sequences: &Vec<ApiSequence>) -> Self {
        let sequences_len = sequences.len();
        if sequences_len <= 0 {
            //println!("Should not merge with no sequence");
            return ApiSequence::new();
        }
        let mut basic_sequence = sequences.first().unwrap().clone();
        for i in 1..sequences_len {
            let other_sequence = &sequences[i];
            basic_sequence = basic_sequence._merge_another_sequence(other_sequence);
        }
        basic_sequence
    }

    pub(crate) fn _contains_api_function(&self, index: usize) -> bool {
        for api_call in &self.functions {
            let (_, func_index) = api_call.func;
            if index == func_index {
                return true;
            }
        }
        return false;
    }

    pub(crate) fn _get_contained_api_functions(&self) -> Vec<usize> {
        let mut res = Vec::new();
        for api_call in &self.functions {
            let (_, func_index) = &api_call.func;
            if !res.contains(func_index) {
                res.push(*func_index);
            }
        }
        res
    }

    pub(crate) fn _is_moved(&self, index: usize) -> bool {
        if self._moved.contains(&index) {
            true
        } else {
            false
        }
    }

    pub(crate) fn _insert_move_index(&mut self, index: usize) {
        self._moved.insert(index);
    }

    pub(crate) fn _add_fn(&mut self, api_call: ApiCall) {
        self.functions.push(api_call);
    }

    pub(crate) fn _insert_fuzzable_mut_tag(&mut self, index: usize) {
        self._fuzzable_mut_tag.insert(index);
    }

    pub(crate) fn _is_fuzzable_need_mut_tag(&self, index: usize) -> bool {
        if self._fuzzable_mut_tag.contains(&index) {
            true
        } else {
            false
        }
    }

    pub(crate) fn _insert_function_mut_tag(&mut self, index: usize) {
        self._function_mut_tag.insert(index);
    }

    pub(crate) fn _is_function_need_mut_tag(&self, index: usize) -> bool {
        if self._function_mut_tag.contains(&index) {
            true
        } else {
            false
        }
    }

    pub(crate) fn set_unsafe(&mut self) {
        self._unsafe_tag = true;
    }

    pub(crate) fn add_trait(&mut self, trait_full_path: &String) {
        self._using_traits.push(trait_full_path.clone());
    }

    pub(crate) fn _is_fuzzables_fixed_length(&self) -> bool {
        for fuzzable_param in &self.fuzzable_params {
            if !fuzzable_param._is_fixed_length() {
                return false;
            }
        }
        return true;
    }

    pub(crate) fn _fuzzables_min_length(&self) -> usize {
        let mut total_length = 0;
        for fuzzable_param in &self.fuzzable_params {
            total_length = total_length + fuzzable_param._min_length();
        }
        total_length
    }

    pub(crate) fn _contains_multi_dynamic_length_fuzzable(&self) -> bool {
        for fuzzable_param in &self.fuzzable_params {
            if fuzzable_param._is_multiple_dynamic_length() {
                return true;
            }
        }
        false
    }

    pub(crate) fn _fuzzable_fixed_part_length(&self) -> usize {
        let mut total_length = 0;
        for fuzzable_param in &self.fuzzable_params {
            total_length = total_length + fuzzable_param._fixed_part_length();
        }
        total_length
    }

    pub(crate) fn _dynamic_length_param_number(&self) -> usize {
        let mut total_number = 0;
        for fuzzable_param in &self.fuzzable_params {
            total_number = total_number + fuzzable_param._dynamic_length_param_number();
        }
        total_number
    }

    pub(crate) fn _dead_code(&self, _api_graph: &ApiGraph<'_>) -> Vec<bool> {
        let sequence_len = self.len();
        let mut dead_api_call = Vec::new();
        for _ in 0..sequence_len {
            dead_api_call.push(true);
        }

        let mut used_params = FxHashMap::default(); // param_index, 最后一次使用这个param的api call index

        let api_call_num = self.functions.len();
        for api_call_index in 0..api_call_num {
            let api_call = &self.functions[api_call_index];
            let params = &api_call.params;
            for (param_type, index, _) in params {
                if let ParamType::_FunctionReturn = param_type {
                    dead_api_call[*index] = false;
                    used_params.insert(*index, api_call_index);
                }
            }
        }

        for api_call_index in 0..api_call_num {
            if !dead_api_call[api_call_index] {
                continue;
            }
            let api_call = &self.functions[api_call_index];
            let params = &api_call.params;
            let param_len = params.len();
            if param_len <= 0 {
                continue;
            }
            let api_function_index = match api_call.func.0 {
                ApiType::BareFunction => api_call.func.1,
            };
            let api_function = &_api_graph.api_functions[api_function_index];
            for param_index in 0..param_len {
                let input_type = &api_function.inputs[param_index];
                let (param_type, index, call_type) = &params[param_index];
                if let ParamType::_FunctionReturn = *param_type {
                    if api_util::_is_mutable_borrow_occurs(input_type, call_type) {
                        if let Some(last_call_index) = used_params.get(index) {
                            if api_call_index < *last_call_index {
                                dead_api_call[api_call_index] = false;
                            }
                        }
                    }
                }
            }
        }

        dead_api_call
    }

    pub(crate) fn _contains_dead_code_except_last_one(&self, _api_graph: &ApiGraph<'_>) -> bool {
        let sequence_len = self.len();
        if sequence_len <= 1 {
            return false;
        }
        let dead_codes = self._dead_code(_api_graph);
        for i in 0..sequence_len - 1 {
            if dead_codes[i] {
                return true;
            }
        }
        return false;
    }

    pub(crate) fn _to_replay_crash_file(
        &self,
        _api_graph: &ApiGraph<'_>,
        test_index: usize,
    ) -> String {
        let mut res = self._to_afl_except_main(_api_graph, test_index);
        res = res.replace("#[macro_use]\nextern crate afl;\n", "");
        res.push_str(replay_util::_read_crash_file_data());
        res.push('\n');
        res.push_str(self._reproduce_main_function(test_index).as_str());
        res
    }

    pub(crate) fn _to_afl_test_file(&self, _api_graph: &ApiGraph<'_>, test_index: usize) -> String {
        let mut res = self._to_afl_except_main(_api_graph, test_index);
        res.push_str(self._afl_main_function(test_index).as_str());
        res
    }

    pub(crate) fn _to_libfuzzer_test_file(
        &self,
        _api_graph: &ApiGraph<'_>,
        test_index: usize,
    ) -> String {
        let mut res = self._to_afl_except_main(_api_graph, test_index);
        res = res.replace(
            "#[macro_use]\nextern crate afl;\n",
            format!("#![no_main]\n#[macro_use]\nextern crate libfuzzer_sys;\n").as_str(),
        );
        res.push_str(self._libfuzzer_fuzz_main(test_index).as_str());
        res
    }

    pub(crate) fn _libfuzzer_fuzz_main(&self, test_index: usize) -> String {
        let mut res = String::new();
        res.push_str("fuzz_target!(|data: &[u8]| {\n");
        res.push_str(self._afl_closure_body(0, test_index).as_str());
        res.push_str("});\n");
        res
    }

    pub(crate) fn _to_afl_except_main(
        &self,
        _api_graph: &ApiGraph<'_>,
        test_index: usize,
    ) -> String {
        let mut res = String::new();
        //加入可能需要开启的feature gate
        let feature_gates = afl_util::_get_feature_gates_of_sequence(&self.fuzzable_params);

        if feature_gates.is_some() {
            for feature_gate in &feature_gates.unwrap() {
                let feature_gate_line = format!("{feature_gate}\n", feature_gate = feature_gate);
                res.push_str(feature_gate_line.as_str());
            }
        }

        res.push_str("#[macro_use]\n");
        res.push_str("extern crate afl;\n");
        res.push_str(format!("extern crate {};\n", _api_graph._crate_name).as_str());

        let prelude_helper_functions = self._prelude_helper_functions();
        if let Some(prelude_functions) = prelude_helper_functions {
            res.push_str(prelude_functions.as_str());
        }

        let afl_helper_functions = self._afl_helper_functions();
        if let Some(afl_functions) = afl_helper_functions {
            res.push_str(afl_functions.as_str());
        }
        res.push_str(self._to_well_written_function(_api_graph, test_index, 0).as_str());
        res.push('\n');
        res
    }

    pub(crate) fn _prelude_helper_functions(&self) -> Option<String> {
        let mut prelude_helpers = FxHashSet::default();
        for api_call in &self.functions {
            let params = &api_call.params;
            for (_, _, call_type) in params {
                let helpers = prelude_type::_PreludeHelper::_from_call_type(call_type);
                for helper in helpers {
                    prelude_helpers.insert(helper);
                }
            }
        }
        if prelude_helpers.len() == 0 {
            return None;
        }
        let mut res = String::new();
        for helper in prelude_helpers {
            res.push_str(helper._to_helper_function());
            res.push('\n');
        }
        Some(res)
    }

    pub(crate) fn _afl_helper_functions(&self) -> Option<String> {
        let afl_helper_functions =
            afl_util::_get_afl_helpers_functions_of_sequence(&self.fuzzable_params);
        match afl_helper_functions {
            None => None,
            Some(afl_helpers) => {
                let mut res = String::new();
                for afl_helper in &afl_helpers {
                    res.push_str(format!("{}\n", afl_helper).as_str());
                }
                Some(res)
            }
        }
    }

    pub(crate) fn _afl_main_function(&self, test_index: usize) -> String {
        let mut res = String::new();
        let indent = _generate_indent(4);
        res.push_str("fn main() {\n");
        res.push_str(indent.as_str());
        res.push_str("fuzz!(|data: &[u8]| {\n");
        res.push_str(self._afl_closure_body(4, test_index).as_str());
        res.push_str(indent.as_str());
        res.push_str("});\n");
        res.push_str("}\n");
        res
    }

    pub(crate) fn _reproduce_main_function(&self, test_index: usize) -> String {
        format!(
            "fn main() {{
    let _content = _read_data();
    let data = &_content;
    println!(\"data = {{:?}}\", data);
    println!(\"data len = {{:?}}\", data.len());
{}
}}",
            self._afl_closure_body(0, test_index)
        )
    }

    pub(crate) fn _afl_closure_body(&self, outer_indent: usize, test_index: usize) -> String {
        let extra_indent = 4;
        let mut res = String::new();
        let indent = _generate_indent(outer_indent + extra_indent);
        res.push_str(format!("{indent}//actual body emit\n", indent = indent).as_str());

        let op = if self._is_fuzzables_fixed_length() { "!=" } else { "<" };
        let min_len = self._fuzzables_min_length();
        res.push_str(
            format!(
                "{indent}if data.len() {op} {min_len} {{return;}}\n",
                indent = indent,
                op = op,
                min_len = min_len
            )
            .as_str(),
        );

        let dynamic_param_start_index = self._fuzzable_fixed_part_length();
        let dynamic_param_number = self._dynamic_length_param_number();
        let dynamic_length_name = "dynamic_length";
        let every_dynamic_length = format!(
            "let {dynamic_length_name} = (data.len() - {dynamic_param_start_index}) / {dynamic_param_number}",
            dynamic_length_name = dynamic_length_name,
            dynamic_param_start_index = dynamic_param_start_index,
            dynamic_param_number = dynamic_param_number
        );
        if !self._is_fuzzables_fixed_length() {
            res.push_str(
                format!(
                    "{indent}{every_dynamic_length};\n",
                    indent = indent,
                    every_dynamic_length = every_dynamic_length
                )
                .as_str(),
            );
        }

        let mut fixed_start_index = 0; //当前固定长度的变量开始分配的位置
        let mut dynamic_param_index = 0; //当前这是第几个动态长度的变量

        let fuzzable_param_number = self.fuzzable_params.len();
        for i in 0..fuzzable_param_number {
            let fuzzable_param = &self.fuzzable_params[i];
            let afl_helper = _AflHelpers::_new_from_fuzzable(fuzzable_param);
            let param_initial_line = afl_helper._generate_param_initial_statement(
                i,
                fixed_start_index,
                dynamic_param_start_index,
                dynamic_param_index,
                dynamic_param_number,
                &dynamic_length_name.to_string(),
                fuzzable_param,
            );
            res.push_str(
                format!(
                    "{indent}{param_initial_line}\n",
                    indent = indent,
                    param_initial_line = param_initial_line
                )
                .as_str(),
            );
            fixed_start_index = fixed_start_index + fuzzable_param._fixed_part_length();
            dynamic_param_index =
                dynamic_param_index + fuzzable_param._dynamic_length_param_number();
        }

        let mut test_function_call =
            format!("{indent}test_function{test_index}(", indent = indent, test_index = test_index);
        for i in 0..fuzzable_param_number {
            if i != 0 {
                test_function_call.push_str(" ,");
            }
            test_function_call.push_str(format!("_param{}", i).as_str());
        }
        test_function_call.push_str(");\n");
        res.push_str(test_function_call.as_str());

        res
    }

    pub(crate) fn _to_well_written_function(
        &self,
        _api_graph: &ApiGraph<'_>,
        test_index: usize,
        indent_size: usize,
    ) -> String {
        let test_function_title = "fn test_function";
        let param_prefix = "_param";
        let local_param_prefix = "_local";
        let mut res = String::new();
        //生成对trait的引用
        let using_traits = self._generate_using_traits_string(indent_size);
        res.push_str(using_traits.as_str());
        //生成函数头
        let function_header = self._generate_function_header_string(
            _api_graph,
            test_index,
            indent_size,
            0,
            test_function_title,
            param_prefix,
        );
        res.push_str(function_header.as_str());

        //加入函数体开头的大括号
        res.push_str("{\n");

        //加入函数体
        if self._unsafe_tag {
            let unsafe_indent = _generate_indent(indent_size + 4);
            res.push_str(unsafe_indent.as_str());
            res.push_str("unsafe {\n");
            let unsafe_function_body = self._generate_function_body_string(
                _api_graph,
                _api_graph.cache(),
                indent_size + 4,
                param_prefix,
                local_param_prefix,
            );
            res.push_str(unsafe_function_body.as_str());
            res.push_str(unsafe_indent.as_str());
            res.push_str("}\n");
        } else {
            let function_body = self._generate_function_body_string(
                _api_graph,
                _api_graph.cache(),
                indent_size,
                param_prefix,
                local_param_prefix,
            );
            res.push_str(function_body.as_str());
        }

        //加入函数体结尾的大括号
        let braket_indent = _generate_indent(indent_size);
        res.push_str(braket_indent.as_str());
        res.push_str("}\n");

        res
    }

    pub(crate) fn _generate_using_traits_string(&self, indent_size: usize) -> String {
        let indent = _generate_indent(indent_size);
        let mut res = String::new();
        //using trait需要去重
        let mut has_used_traits = FxHashSet::default();
        for using_trait_ in &self._using_traits {
            if has_used_traits.contains(using_trait_) {
                continue;
            } else {
                has_used_traits.insert(using_trait_.clone());
            }
            res.push_str(indent.as_str());
            res.push_str("use ");
            res.push_str(using_trait_.as_str());
            res.push_str(";\n");
        }
        res.push('\n');
        res
    }

    //outer_indent:上层的缩进
    //extra_indent:本块需要的额外缩进
    pub(crate) fn _generate_function_header_string(
        &self,
        _api_graph: &ApiGraph<'_>,
        test_index: usize,
        outer_indent: usize,
        extra_indent: usize,
        test_function_title: &str,
        param_prefix: &str,
    ) -> String {
        let indent_size = outer_indent + extra_indent;
        let indent = _generate_indent(indent_size);

        //生成具体的函数签名
        let mut res = String::new();
        res.push_str(indent.as_str());
        res.push_str(test_function_title);
        res.push_str(test_index.to_string().as_str());
        res.push_str("(");

        //加入所有的fuzzable变量
        //第一个参数特殊处理
        let first_param = self.fuzzable_params.first();
        if let Some(first_param_) = first_param {
            if self._is_fuzzable_need_mut_tag(0) {
                res.push_str("mut ");
            }
            res.push_str(param_prefix);
            res.push('0');
            res.push_str(" :");
            res.push_str(first_param_._to_type_string().as_str());
        }

        let param_size = self.fuzzable_params.len();
        for i in 1..param_size {
            res.push_str(" ,");
            if self._is_fuzzable_need_mut_tag(i) {
                res.push_str("mut ");
            }
            let param = &self.fuzzable_params[i];
            res.push_str(param_prefix);
            res.push_str(i.to_string().as_str());
            res.push_str(" :");
            res.push_str(param._to_type_string().as_str());
        }
        res.push_str(") ");
        res
    }

    pub(crate) fn _generate_function_body_string(
        &self,
        _api_graph: &ApiGraph<'_>,
        cache: &Cache,
        outer_indent: usize,
        param_prefix: &str,
        local_param_prefix: &str,
    ) -> String {
        let extra_indent = 4;
        let mut res = String::new();
        let body_indent = _generate_indent(outer_indent + extra_indent);

        let dead_code = self._dead_code(_api_graph);

        //api_calls
        let api_calls_num = self.functions.len();
        let full_name_map = &_api_graph.full_name_map;
        for i in 0..api_calls_num {
            let api_call = &self.functions[i];

            //准备参数
            let param_size = api_call.params.len();
            let mut param_strings = Vec::new();
            for j in 0..param_size {
                let (param_type, index, call_type) = &api_call.params[j];
                let call_type_array = call_type._split_at_unwrap_call_type();
                //println!("call_type_array = {:?}",call_type_array);
                let param_name = match param_type {
                    ParamType::_FuzzableType => {
                        let mut s1 = param_prefix.to_string();
                        s1 += &(index.to_string());
                        s1
                    }
                    ParamType::_FunctionReturn => {
                        let mut s1 = local_param_prefix.to_string();
                        s1 += &(index.to_string());
                        s1
                    }
                };
                let call_type_array_len = call_type_array.len();
                if call_type_array_len == 1 {
                    let call_type = &call_type_array[0];
                    let param_string = call_type._to_call_string(&param_name, full_name_map, cache);
                    param_strings.push(param_string);
                } else {
                    let mut former_param_name = param_name.clone();
                    let mut helper_index = 1;
                    let mut former_helper_line = String::new();
                    for k in 0..call_type_array_len - 1 {
                        let call_type = &call_type_array[k];
                        let helper_name = format!(
                            "{}{}_param{}_helper{}",
                            local_param_prefix, i, j, helper_index
                        );
                        let helper_line = format!(
                            "{}let mut {} = {};\n",
                            body_indent,
                            helper_name,
                            call_type._to_call_string(&former_param_name, full_name_map, cache)
                        );
                        if helper_index > 1 {
                            if !api_util::_need_mut_tag(call_type) {
                                former_helper_line = former_helper_line.replace("let mut ", "let ");
                            }
                            res.push_str(former_helper_line.as_str());
                        }
                        helper_index = helper_index + 1;
                        former_param_name = helper_name;
                        former_helper_line = helper_line;
                    }
                    let last_call_type = call_type_array.last().unwrap();
                    if !api_util::_need_mut_tag(last_call_type) {
                        former_helper_line = former_helper_line.replace("let mut ", "let ");
                    }
                    res.push_str(former_helper_line.as_str());
                    let param_string =
                        last_call_type._to_call_string(&former_param_name, full_name_map, cache);
                    param_strings.push(param_string);
                }
            }
            res.push_str(body_indent.as_str());
            //如果不是最后一个调用
            let api_function_index = api_call.func.1;
            let api_function = &_api_graph.api_functions[api_function_index];
            if dead_code[i] || api_function._has_no_output() {
                res.push_str("let _ = ");
            } else {
                let mut_tag = if self._is_function_need_mut_tag(i) { "mut " } else { "" };
                res.push_str(format!("let {}{}{} = ", mut_tag, local_param_prefix, i).as_str());
            }
            let (api_type, function_index) = &api_call.func;
            match api_type {
                ApiType::BareFunction => {
                    let api_function_full_name =
                        &_api_graph.api_functions[*function_index].full_name;
                    res.push_str(api_function_full_name.as_str());
                }
            }
            res.push('(');

            let param_size = param_strings.len();
            for k in 0..param_size {
                if k != 0 {
                    res.push_str(" ,");
                }

                let param_string = &param_strings[k];
                res.push_str(param_string.as_str());
            }
            res.push_str(");\n");
        }
        res
    }
}

pub(crate) fn _generate_indent(indent_size: usize) -> String {
    let mut indent = String::new();
    for _ in 0..indent_size {
        indent.push(' ');
    }
    indent
}
