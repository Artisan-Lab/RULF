//This file contains functions to print intermediate info

use crate::fuzz_target::api_graph::ApiGraph;
use crate::fuzz_target::api_graph::ApiType;
use crate::fuzz_target::type_name::TypeNameLevel;
use crate::fuzz_target::type_name::type_full_name;

/// traits of primitive types

//print generated sequences
pub fn _print_pretty_sequences(graph: &ApiGraph) {
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

pub fn _print_pretty_functions(graph: &ApiGraph, check_visited: bool) {
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
        let fn_line = api_function._pretty_print(&graph.full_name_map);

        println!("{}:{}", i, fn_line);
    }
}

pub fn _print_pretty_dependencies(graph: &ApiGraph) {
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

pub fn _print_generated_test_functions(graph: &ApiGraph) {
    println!("test_functions:");
    let test_size = graph.api_sequences.len();
    for i in 0..test_size {
        let api_sequence = &graph.api_sequences[i];
        println!("{}", api_sequence._to_well_written_function(graph, i, 0));
    }
}

pub fn _print_generated_afl_file(graph: &ApiGraph) {
    println!("afl_files:");
    let test_size = graph.api_sequences.len();
    for i in 0..test_size {
        let api_sequence = &graph.api_sequences[i];
        println!("{}", api_sequence._to_afl_test_file(graph, i));
        //break;
    }
}

//libfuzzer is not supported now
pub fn _print_generated_libfuzzer_file(graph: &ApiGraph) {
    println!("libfuzzer files");
    let test_size = graph.api_sequences.len();
    for i in 0..test_size {
        let api_sequence = &graph.api_sequences[i];
        println!("{}", api_sequence._to_libfuzzer_test_file(graph, i));
    }
}

pub fn _print_generic_functions(graph: &ApiGraph) {
    println!("generic functions");
    graph.generic_functions.iter().for_each(|generic_function| {
        println!("{}", generic_function.api_function.full_name);
        println!("{:?}", generic_function.type_bounds);
        generic_function.api_function.inputs.iter().for_each(|input| {
            println!("{:?}", input);
        });
    });
}

pub fn _print_type_in_current_crate(graph: &ApiGraph) {
    println!("Type in current crate:");
    graph.types_in_current_crate.type_full_names.iter().for_each(|(did, full_name)| {
        println!("full name: {}", full_name);
        if let Some(bounds) = graph.types_in_current_crate.traits_of_type.get(did) {
            println!("bounds of type: {}", full_name);
            bounds.iter().for_each(|type_| {
                println!("{:?}", type_);
            });
        }
    });
}

pub fn _print_traits_in_current_crate(graph: &ApiGraph) {
    println!("traits_in_current_crate:");
    graph.types_in_current_crate.traits.iter().for_each(|(_, trait_name)| {
        println!("{}", trait_name);
    });
}

pub fn _print_type_full_names(graph: &ApiGraph) {
    println!("type_full_names");
    graph.api_functions.iter().for_each(|api_func| {
        println!("Function name: {}", api_func.full_name);
        api_func.inputs.iter().for_each(|input| {
            println!("{}", type_full_name(input, &graph.type_name_map, TypeNameLevel::All))
        });
        api_func.output.iter().for_each(|output| {
            println!("{}", type_full_name(output, &graph.type_name_map, TypeNameLevel::All))
        });
    });
}