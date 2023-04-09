//This file cratecontains functions to print intermediate info

use crate::formats::cache::Cache;
use crate::fuzz_target::api_graph::ApiGraph;
use crate::fuzz_target::api_graph::ApiType;

//print generated sequences
pub(crate) fn _print_pretty_sequences(graph: &ApiGraph<'_>) {
    println!("sequences:");
    for api_sequence in &graph.api_sequences {
        let mut one_sequence = String::new();
        for api_call in &api_sequence.functions {
            let (api_type, index) = &api_call.func;
            match api_type {
                ApiType::BareFunction => {
                    let func = &graph.api_functions[*index];
                    let func_name = func.full_name.clone();
                    one_sequence.push_str(func_name.as_str());
                    one_sequence.push_str(" ");
                }
            }
        }
        println!("{:?}", one_sequence);
    }
}

pub(crate) fn _print_pretty_functions(graph: &ApiGraph<'_>, cache:&Cache, check_visited: bool) {
    println!("functions");
    let api_functions_num = graph.api_functions.len();
    for i in 0..api_functions_num {
        if check_visited {
            //如果需要check visited，只输出没有被覆盖到的函数
            if graph.api_functions_visited[i] {
                continue;
            }
        }
        let api_function = &graph.api_functions[i];
        let fn_line = api_function._pretty_print(&graph.full_name_map, cache);

        println!("{}:{}", i, fn_line);
    }
}

pub(crate) fn _print_pretty_dependencies(graph: &ApiGraph<'_>) {
    println!("dependencies:");
    println!("function number: {:?}", graph.api_functions.len());
    for dependency in &graph.api_dependencies {
        let (output_type, output_index) = &dependency.output_fun;
        let (input_type, input_index) = &dependency.input_fun;
        let mut res = String::new();
        match output_type {
            ApiType::BareFunction => {
                let output_fun = &graph.api_functions[*output_index];
                res.push_str(output_fun.full_name.as_str());
            }
        }
        res.push_str(" ");
        match input_type {
            ApiType::BareFunction => {
                let input_fun = &graph.api_functions[*input_index];
                res.push_str(input_fun.full_name.as_str());
            }
        }
        res.push_str(" ");
        res.push_str(dependency.input_param_index.to_string().as_str());
        res.push_str(" ");
        print!("{:?}", res);
        println!("{:?}", dependency.call_type);
        //res.push_str("\r\n");
    }
}

pub(crate) fn _print_generated_test_functions(graph: &ApiGraph<'_>) {
    println!("test_functions:");
    let test_size = graph.api_sequences.len();
    for i in 0..test_size {
        let api_sequence = &graph.api_sequences[i];
        println!("{}", api_sequence._to_well_written_function(graph, i, 0,));
    }
}

pub(crate) fn _print_generated_afl_file(graph: &ApiGraph<'_>) {
    println!("afl_files:");
    let test_size = graph.api_sequences.len();
    for i in 0..test_size {
        let api_sequence = &graph.api_sequences[i];
        println!("{}", api_sequence._to_afl_test_file(graph, i));
        //break;
    }
}

//libfuzzer is not supported now
pub(crate) fn _print_generated_libfuzzer_file(graph: &ApiGraph<'_>) {
    println!("libfuzzer files");
    let test_size = graph.api_sequences.len();
    for i in 0..test_size {
        let api_sequence = &graph.api_sequences[i];
        println!("{}", api_sequence._to_libfuzzer_test_file(graph, i));
    }
}

pub(crate) fn _print_generic_functions(graph: &ApiGraph<'_>) {
    println!("generic functions");
    graph.generic_functions.iter().for_each(|generic_function| {
        println!("{}", generic_function.api_function.full_name);
    });
}
