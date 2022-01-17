use std::collections::{HashSet, HashMap};
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_hir::def::{Res, DefKind};
use crate::clean;
use crate::html::render::cache::Cache;

pub fn get_qpaths_in_clean_type(clean_type: &clean::Type) -> HashSet<clean::Type> {
    let mut res = HashSet::new();
    match clean_type.to_owned() {
        clean::Type::QPath {..} => {
            res.insert(clean_type.to_owned());
            res
        },
        clean::Type::Array(type_, ..) | clean::Type::BorrowedRef { type_,.. } |
        clean::Type::Slice(type_,..) | clean::Type::RawPointer(_, type_) => {
            get_qpaths_in_clean_type(&*type_)
        },
        clean::Type::Tuple(types) => {
            types.iter().for_each(|type_| {
                res.extend(get_qpaths_in_clean_type(type_));
            });
            res
        },
        clean::Type::ResolvedPath { path, .. } => {
            let segments= path.segments;
            segments.into_iter().for_each(|path_segment| {
                let args = path_segment.args;
                match args {
                    clean::GenericArgs::AngleBracketed {args, ..} => {
                        args.iter().for_each(|generic_arg| {
                            if let clean::GenericArg::Type(type_) = generic_arg {
                                res.extend(get_qpaths_in_clean_type(&type_));
                            }
                        });
                    },
                    clean::GenericArgs::Parenthesized{inputs, output} => {
                        inputs.iter().for_each(|type_| {
                            res.extend(get_qpaths_in_clean_type(&type_));
                        });
                        output.iter().for_each(|type_| {
                            res.extend(get_qpaths_in_clean_type(&type_));
                        });
                    }
                };
            });
            res
        },
        _ => res,
    }
}

pub fn get_generics_of_clean_type(ty_: &clean::Type) -> HashSet<String> {
    let mut res = HashSet::new();
    match ty_ {
        clean::Type::Generic(generic_name) => {
            res.insert(generic_name.to_owned());
            return res;
        },
        clean::Type::ResolvedPath { .. } => {
            ty_.generics().iter().for_each(|types| {
                types.iter().for_each(|type_| {
                    let generics = get_generics_of_clean_type(type_);
                    res.extend(generics);
                });
            });
            return res;
        },
        clean::Type::BorrowedRef {type_,..} | clean::Type::Slice(type_) 
        | clean::Type::Array(type_,.. ) | clean::Type::RawPointer(_, type_) => {
            let generics = get_generics_of_clean_type(&**type_);
            res.extend(generics);
            return res;
        },
        clean::Type::Tuple(types) => {
            types.iter().for_each(|type_| {
                let generics = get_generics_of_clean_type(type_);
                res.extend(generics);
            });
            return res;
        },
        _ => res,
    }
}

/// convert clean::struct to clean::Type. We currently don't consider generics
pub fn from_struct_to_clean_type(did: DefId, name: String) -> clean::Type {
    let res = Res::Def(DefKind::Struct, did);
    let args = clean::GenericArgs::AngleBracketed{args: Vec::new(), bindings: Vec::new()};
    let path_segment = clean::PathSegment{name, args};
    let segments = vec![path_segment];
    let path = clean::Path {global:false, res, segments};
    clean::Type::ResolvedPath{path, param_names: None, did, is_generic: false}
}

pub fn from_enum_to_clean_type(did: DefId, name: String) -> clean::Type {
    let res = Res::Def(DefKind::Enum, did);
    let args = clean::GenericArgs::AngleBracketed{args: Vec::new(), bindings: Vec::new()};
    let path_segment = clean::PathSegment{name, args};
    let segments = vec![path_segment];
    let path = clean::Path {global:false, res, segments};
    clean::Type::ResolvedPath{path, param_names: None, did, is_generic: false}
}

pub fn generics_has_no_content(generics: &clean::Generics) -> bool {
    generics.params.len() == 0 && generics.where_predicates.len() == 0
}

pub fn collect_traits_in_current_crate(cache: &Cache) -> HashMap<DefId, String> {
    let mut res = HashMap::new();
    cache.traits.iter().for_each(|(def_id, _)| {
        // trait in current crate
        if let Some(path) = cache.exact_paths.get(&def_id) {
            let path = path.iter().join("::");
            res.insert(*def_id, path);
        }
        if let Some(path) = cache.external_paths.get(&def_id) {
            let path = path.0.iter().join("::");
            res.insert(*def_id, path);
        }
    });
    res
}

/// replace types in raw_type with replace_type_map
pub fn replace_types(raw_type: &clean::Type, replace_type_map: &HashMap<clean::Type, clean::Type>) -> clean::Type {
    if replace_type_map.contains_key(raw_type) {
        return replace_type_map.get(raw_type).unwrap().to_owned();
    }

    match raw_type.to_owned() {
        clean::Type::RawPointer(mutability, inner_type) => {
            let new_type = replace_types(&*inner_type, replace_type_map);
            clean::Type::RawPointer(mutability, Box::new(new_type))
        },
        clean::Type::BorrowedRef { lifetime, mutability, type_ } => {
            let new_type = replace_types(&*type_, replace_type_map);
            clean::Type::BorrowedRef{lifetime, mutability, type_:Box::new(new_type)}
        },
        clean::Type::Slice(inner_type) => {
            let new_type = replace_types(&*inner_type, replace_type_map);
            clean::Type::Slice(Box::new(new_type))
        }, 
        clean::Type::Array(inner_type, length) => {
            let new_type = replace_types(&*inner_type, replace_type_map);
            clean::Type::Array(Box::new(new_type), length)
        },
        clean::Type::Tuple(types) => {
            let new_types = types.into_iter().map(|type_| {
                replace_types(&type_, replace_type_map)
            }).collect_vec();
            clean::Type::Tuple(new_types)
        },
        clean::Type::ResolvedPath { path, param_names, did, is_generic } => {
            let clean::Path{global, res, segments} = path;
            let new_segments = segments.into_iter().map(|path_segment| {
                let clean::PathSegment{name, args} = path_segment;
                let new_args = match args {
                    clean::GenericArgs::AngleBracketed {args, bindings} => {
                        let new_args = args.into_iter().map(|generic_arg| {
                            if let clean::GenericArg::Type(type_) = generic_arg {
                                let new_type = replace_types(&type_, replace_type_map);
                                clean::GenericArg::Type(new_type)
                            } else {
                                generic_arg
                            }
                        }).collect_vec();
                        clean::GenericArgs::AngleBracketed {args: new_args, bindings}
                    },
                    clean::GenericArgs::Parenthesized{inputs, output} => {
                        let new_inputs = inputs.into_iter().map(|type_| {
                            replace_types(&type_, replace_type_map)
                        }).collect_vec();
                        let new_output = output.map(|type_| {
                            replace_types(&type_, replace_type_map)
                        });
                        clean::GenericArgs::Parenthesized{inputs: new_inputs, output: new_output}
                    }
                };
                clean::PathSegment{name, args: new_args}
            }).collect_vec();
            let new_path = clean::Path{global, res, segments: new_segments};
            clean::Type::ResolvedPath{path: new_path, param_names, did, is_generic}
        }
        _ => raw_type.to_owned(),
    }
}