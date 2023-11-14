use crate::clean::{GenericArg, GenericArgs};
use crate::clean::{Path, Type};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_util::{
    _type_name, get_type_name_from_did, replace_type_with, type_depth,
};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};

pub(crate) fn take_type_from_path(path: &Path, no: usize) -> Type {
    if let GenericArgs::AngleBracketed { ref args, .. } = path.segments.last().unwrap().args {
        if let GenericArg::Type(ref ty) = args[no] {
            return ty.clone();
        }
        unreachable!();
    } else {
        unreachable!();
    }
}

pub(crate) type Solution = Vec<Type>;

pub(crate) fn get_param_index(name: &str, generic_defs: &Vec<String>) -> usize {
    for i in 0..generic_defs.len() {
        if generic_defs[i] == name {
            return i;
        }
    }
    unreachable!("unknown generic param: {}", name);
}

pub(crate) fn solution_string_with_param_name(
    solution: &Solution,
    generic_defs: &Vec<String>,
) -> String {
    assert!(generic_defs.len() == solution.len());
    let mut strs = Vec::<String>::new();
    for i in 0..solution.len() {
        let ty_str = match solution[i] {
            Type::Infer => "*".to_string(),
            _ => _type_name(&solution[i], None),
        };
        strs.push(format!("{}={}", generic_defs[i], ty_str));
    }
    format!("({})", strs.join(", "))
}

pub(crate) fn solution_string(solution: &Solution) -> String {
    let mut strs = Vec::<String>::new();
    for ty in solution.iter() {
        let ty_str = match ty {
            Type::Infer => "*".to_string(),
            _ => _type_name(ty, None),
        };
        strs.push(ty_str);
    }
    format!("({})", strs.join(", "))
}

pub(crate) fn solution_set_string(solution_set: &Vec<Solution>) -> String {
    let mut strs = Vec::<String>::new();
    for solution in solution_set.iter() {
        strs.push(solution_string(solution));
    }
    format!("`{}`", strs.join(", "))
}

pub(crate) fn default_solution(len: usize) -> Solution {
    vec![Type::Infer; len]
}

pub(crate) fn merge_solution(
    sol_a: &Solution,
    sol_b: &Solution,
    generic_defs: &Vec<String>,
) -> Option<Solution> {
    assert!(sol_a.len() == sol_b.len() && sol_a.len() == generic_defs.len());
    let mut sol = vec![Type::Infer; sol_a.len()];
    for i in 0..sol_a.len() {
        if sol_a[i] == Type::Infer {
            sol[i] = sol_b[i].clone();
        } else if sol_b[i] == Type::Infer {
            sol[i] = sol_a[i].clone();
        } else if match_type(&sol_a[i], &sol_b[i], generic_defs).is_some() {
            sol[i] = sol_a[i].clone();
        } else {
            return None;
        }
    }
    Some(sol)
}

pub(crate) fn merge_solution_set(
    a: &Vec<Solution>,
    b: &Vec<Solution>,
    generic_defs: &Vec<String>,
) -> Vec<Solution> {
    let mut res = Vec::new();
    for sol_a in a.iter() {
        for sol_b in b.iter() {
            assert!(sol_a.len() == generic_defs.len() && sol_b.len() == generic_defs.len());
            if let Some(sol) = merge_solution(sol_a, sol_b, generic_defs) {
                res.push(sol);
            }
        }
    }
    println!("set A: {}", solution_set_string(&a));
    println!("set B: {}", solution_set_string(&b));
    println!("Merge: {}", solution_set_string(&res));
    res
}

pub(crate) fn check_solution_depth(solution: &Solution, depth: usize) -> bool {
    for type_ in solution.iter() {
        if type_depth(type_) > depth {
            return false;
        }
    }
    true
}

/// pattern type may contain generic args,
/// however, source type must be concrete
/// 
/// Returns [`None`] if source does not match pattern.
/// Otherwise return the solution
pub(crate) fn match_type(
    source: &Type,
    pattern: &Type,
    generic_defs: &Vec<String>,
) -> Option<Solution> {
    // print!("[match] compare {} - {}, {:?}\n", _type_name(source, None), _type_name(pattern, None), generic_defs);
    let mut map = default_solution(generic_defs.len());
    let mut merge_with_inner = |inner: Option<Vec<Type>>| -> bool {
        if let Some(inner_map) = inner {
            for (i, item) in inner_map.into_iter().enumerate() {
                if map[i] == Type::Infer {
                    map[i] = item;
                } else if item != Type::Infer && item != map[i] {
                    return false;
                }
            }
            return true;
        }
        false
    };
    if source == pattern {
        return Some(map);
    }
    match (source, pattern) {
        (Type::Generic(_), _) | (Type::Infer, _) => {
            unreachable!("source have invalid type: {}", _type_name(source, None));
        }
        (_, Type::Generic(sym)) => {
            let no = get_param_index(sym.as_str(), generic_defs);
            map[no] = source.clone();
        }
        (Type::Tuple(srcs), Type::Tuple(pats)) => {
            if srcs.len() != pats.len() {
                return None;
            }
            for i in 0..srcs.len() {
                let src = &srcs[i];
                let pat = &pats[i];
                let inner_map = match_type(src, pat, generic_defs);
                if (!merge_with_inner(inner_map)) {
                    return None;
                }
            }
        }
        (Type::Slice(src), Type::Slice(pat))
        | (Type::Array(src, ..), Type::Array(pat, ..))
        | (Type::RawPointer(_, src), Type::RawPointer(_, pat)) => {
            let inner_map = match_type(src, pat, generic_defs);
            if (!merge_with_inner(inner_map)) {
                return None;
            }
        }
        (
            Type::BorrowedRef { type_: src, mutability: mut_src, .. },
            Type::BorrowedRef { type_: pat, mutability: mut_pat, .. },
        ) => {
            if mut_src != mut_pat {
                return None;
            }
            let inner_map = match_type(src, pat, generic_defs);
            if (!merge_with_inner(inner_map)) {
                return None;
            }
        }
        (Type::Primitive(src), Type::Primitive(pat)) => {
            if *src != *pat {
                return None;
            }
        }
        (Type::Path { path: src_path }, Type::Path { path: pat_path }) => {
            if (src_path.def_id() != pat_path.def_id())
            {
                // println!("[match] unmatch fail#0: {:?} {:?} {} {}", src_path.def_id(), pat_path.def_id(),src_path.segments.len(),pat_path.segments.len());
                return None;
            }

            if let (Some(src_segment),Some(pat_segment)) = (src_path.segments.last(), pat_path.segments.last()){
                /* let src_segment = &src_path.segments[i];
                let pat_segment = &pat_path.segments[i]; */
                if src_segment.name.to_string() != pat_segment.name.to_string() {
                    // println!("[match] unmatch fail#1");
                    return None;
                }
                match (&src_segment.args, &pat_segment.args) {
                    (
                        GenericArgs::AngleBracketed { args: src_args, .. },
                        GenericArgs::AngleBracketed { args: pat_args, .. },
                    ) => {
                        if src_args.len() != pat_args.len() {
                            return None;
                        }
                        for j in 0..src_args.len() {
                            let src_arg = &src_args[j];
                            let pat_arg = &pat_args[j];
                            if let (GenericArg::Type(src), GenericArg::Type(pat)) =
                                (src_arg, pat_arg)
                            {
                                let inner_map = match_type(src, pat, generic_defs);
                                if (!merge_with_inner(inner_map)) {
                                    // println!("[match] unmatch fail#2");
                                    return None;
                                }
                            } // ignore other variant of GenericArg
                        }
                    }
                    (GenericArgs::Parenthesized { .. }, GenericArgs::Parenthesized { .. }) => {}
                    _ => {
                        // println!("[match] unmatch fail#3");
                        return None;
                    }
                }
            } else {
                unreachable!("NO segment? {:?} {:?}",src_path,pat_path)
            }
            
        }
        _ => {
            return None;
        }
    }
    Some(map)
}

pub(crate) fn match_call_type(
    source: &Type,
    pattern: &Type,
    generic_defs: &Vec<String>,
    cache: &Cache,
) -> Option<Solution> { 
    // try direct match
    let res = match_type(source, pattern, generic_defs);
    if res.is_some() {
        return res;
    }

    // We have canonical source, so we don't need try to unwrap source
    
    let mut unwrap_pattern = pattern.clone();

    loop {
        unwrap_pattern = match unwrap_pattern {
            Type::Path { ref path } => {
                let name = get_type_name_from_did(path.def_id(), cache);
                // let name = path.segments.last().unwrap().name.to_string();
                if name == "core::option::Option" {
                    take_type_from_path(path, 0)
                } else if name == "core::result::Result" {
                    take_type_from_path(path, 0)
                } else {
                    break;
                }
            }
            _ => break,
        };
    }

    let res = match_type(&source, &unwrap_pattern, generic_defs);

    if res.is_some() {
        return res;
    }

    None
}

pub(crate) fn replace_generic_with_solution(
    type_: &mut Type,
    solution: &Solution,
    generic_defs: &Vec<String>,
) {
    let mut replace = |type_: &mut Type| -> bool {
        if let Type::Generic(sym) = type_ {
            let name = sym.as_str();
            for i in 0..generic_defs.len() {
                if generic_defs[i] == name {
                    *type_ = solution[i].clone();
                    // return Some(solution[i].clone());
                    return false;
                }
            }
            unreachable!("unknown generic param: {}", name);
        }
        true
    };
    replace_type_with(type_, &mut replace);
}
