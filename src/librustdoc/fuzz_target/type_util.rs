use crate::clean::{self, Path};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_util::is_generic_type;
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::DefId;
use rustc_hir::Mutability;

pub fn get_qpaths_in_clean_type(clean_type: &clean::Type) -> FxHashSet<clean::Type> {
    let mut res = FxHashSet::default();
    match clean_type.to_owned() {
        clean::Type::QPath { .. } => {
            res.insert(clean_type.to_owned());
            res
        }
        clean::Type::Array(type_, ..)
        | clean::Type::BorrowedRef { type_, .. }
        | clean::Type::Slice(type_, ..)
        | clean::Type::RawPointer(_, type_) => get_qpaths_in_clean_type(&*type_),
        clean::Type::Tuple(types) => {
            types.iter().for_each(|type_| {
                res.extend(get_qpaths_in_clean_type(type_));
            });
            res
        }
        clean::Type::Path { path, .. } => {
            let segments = path.segments;
            segments.into_iter().for_each(|path_segment| {
                let args = path_segment.args;
                match args {
                    clean::GenericArgs::AngleBracketed { args, .. } => {
                        args.iter().for_each(|generic_arg| {
                            if let clean::GenericArg::Type(type_) = generic_arg {
                                res.extend(get_qpaths_in_clean_type(&type_));
                            }
                        });
                    }
                    clean::GenericArgs::Parenthesized { inputs, output } => {
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
        }
        _ => res,
    }
}

pub fn get_generics_of_clean_type(clean_type: &clean::Type) -> FxHashSet<String> {
    let mut res = FxHashSet::default();
    match clean_type {
        clean::Type::Generic(generic_name) => {
            res.insert(generic_name.to_owned());
            return res;
        }
        clean::Type::Path { .. } => {
            clean_type.generics().iter().for_each(|types| {
                types.iter().for_each(|type_| {
                    let generics = get_generics_of_clean_type(type_);
                    res.extend(generics);
                });
            });
            return res;
        }
        clean::Type::BorrowedRef { type_, .. }
        | clean::Type::Slice(type_)
        | clean::Type::Array(type_, ..)
        | clean::Type::RawPointer(_, type_) => {
            let generics = get_generics_of_clean_type(&**type_);
            res.extend(generics);
            return res;
        }
        clean::Type::Tuple(types) => {
            types.iter().for_each(|type_| {
                let generics = get_generics_of_clean_type(type_);
                res.extend(generics);
            });
            return res;
        }
        _ => res,
    }
}

/// convert clean::struct to clean::Type. We currently don't consider generics
pub fn from_struct_to_clean_type(did: DefId, name: String) -> clean::Type {
    let res = Res::Def(DefKind::Struct, did);
    let args = clean::GenericArgs::AngleBracketed { args: Vec::new(), bindings: Vec::new() };
    let path_segment = clean::PathSegment { name, args };
    let segments = vec![path_segment];
    let path = clean::Path { res, segments };
    clean::Type::Path { path }
}

pub fn from_enum_to_clean_type(did: DefId, name: String) -> clean::Type {
    let res = Res::Def(DefKind::Enum, did);
    let args = clean::GenericArgs::AngleBracketed { args: Vec::new(), bindings: Vec::new() };
    let path_segment = clean::PathSegment { name, args };
    let segments = vec![path_segment];
    let path = clean::Path { res, segments };
    clean::Type::Path { path }
}

pub fn generics_has_no_content(generics: &clean::Generics) -> bool {
    generics.params.len() == 0 && generics.where_predicates.len() == 0
}

pub fn collect_traits_in_current_crate(cache: &Cache) -> FxHashMap<DefId, String> {
    let mut res = FxHashMap::default();
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
pub fn replace_types(
    raw_type: &clean::Type,
    replace_type_map: &FxHashMap<clean::Type, clean::Type>,
) -> clean::Type {
    if replace_type_map.contains_key(raw_type) {
        return replace_type_map.get(raw_type).unwrap().to_owned();
    }

    match raw_type.to_owned() {
        clean::Type::RawPointer(mutability, inner_type) => {
            let new_type = replace_types(&*inner_type, replace_type_map);
            clean::Type::RawPointer(mutability, Box::new(new_type))
        }
        clean::Type::BorrowedRef { lifetime, mutability, type_ } => {
            let new_type = replace_types(&*type_, replace_type_map);
            clean::Type::BorrowedRef { lifetime, mutability, type_: Box::new(new_type) }
        }
        clean::Type::Slice(inner_type) => {
            let new_type = replace_types(&*inner_type, replace_type_map);
            clean::Type::Slice(Box::new(new_type))
        }
        clean::Type::Array(inner_type, length) => {
            let new_type = replace_types(&*inner_type, replace_type_map);
            clean::Type::Array(Box::new(new_type), length)
        }
        clean::Type::Tuple(types) => {
            let new_types = types
                .into_iter()
                .map(|type_| replace_types(&type_, replace_type_map))
                .collect_vec();
            clean::Type::Tuple(new_types)
        }
        clean::Type::Path { path } => {
            let clean::Path { res, segments } = path;
            let new_segments = segments
                .into_iter()
                .map(|path_segment| {
                    let clean::PathSegment { name, args } = path_segment;
                    let new_args = match args {
                        clean::GenericArgs::AngleBracketed { args, bindings } => {
                            let new_args = args
                                .into_iter()
                                .map(|generic_arg| {
                                    if let clean::GenericArg::Type(type_) = generic_arg {
                                        let new_type = replace_types(&type_, replace_type_map);
                                        clean::GenericArg::Type(new_type)
                                    } else {
                                        generic_arg
                                    }
                                })
                                .collect_vec();
                            clean::GenericArgs::AngleBracketed { args: new_args, bindings }
                        }
                        clean::GenericArgs::Parenthesized { inputs, output } => {
                            let new_inputs = inputs
                                .into_iter()
                                .map(|type_| replace_types(&type_, replace_type_map))
                                .collect_vec();
                            let new_output =
                                output.map(|type_| replace_types(&type_, replace_type_map));
                            clean::GenericArgs::Parenthesized {
                                inputs: new_inputs,
                                output: new_output,
                            }
                        }
                    };
                    clean::PathSegment { name, args: new_args }
                })
                .collect_vec();
            let new_path = clean::Path { res, segments: new_segments };
            clean::Type::Path { path: new_path }
        }
        _ => raw_type.to_owned(),
    }
}

pub fn extract_only_one_type_parameter(trait_bound: &clean::Type) -> Option<clean::Type> {
    let path = if let clean::Type::Path { path, .. } = trait_bound {
        path
    } else {
        return None;
    };
    let segments = &path.segments;
    for path_segment in segments {
        let generic_args = &path_segment.args;
        match generic_args {
            clean::GenericArgs::AngleBracketed { args, .. } => {
                if args.len() != 1 {
                    continue;
                }
                let arg = &args[0];
                if let clean::GenericArg::Type(type_) = arg {
                    if !is_generic_type(type_) {
                        return Some(type_.to_owned());
                    } else {
                        error!("Internal Error: Found Generic in trait");
                    }
                }
            }
            clean::GenericArgs::Parenthesized { .. } => {}
        }
    }
    return None;
}

// extract all occurred types in a type
pub fn extract_types(ty_: &clean::Type) -> FxHashSet<clean::Type> {
    match ty_ {
        clean::Type::Primitive(..)
        | clean::Type::BareFunction(..)
        | clean::Type::Generic(..)
        | clean::Type::ImplTrait(..)
        | clean::Type::QPath { .. }
        | clean::Type::Infer => FxHashSet::default(),
        clean::Type::Path { path, .. } => {
            let mut path_types = extract_types_in_path(path);
            path_types.insert(ty_.to_owned());
            path_types
        }
        clean::Type::Array(type_, ..) => extract_types(&**type_),
        clean::Type::BorrowedRef { type_, .. } => extract_types(&**type_),
        clean::Type::RawPointer(_, type_) => extract_types(&**type_),
        clean::Type::Slice(type_) => extract_types(&**type_),
        clean::Type::Tuple(types) => {
            types.iter().map(|type_| extract_types(type_)).fold(FxHashSet::default(), |mut l, r| {
                l.extend(r);
                l
            })
        }
    }
}

fn extract_types_in_path(path: &Path) -> FxHashSet<clean::Type> {
    let mut res = FxHashSet::default();
    for segments in path.segments.iter() {
        if let clean::GenericArgs::AngleBracketed { ref args, .. } = segments.args {
            args.iter().for_each(|generic_arg| {
                if let clean::GenericArg::Type(ty_) = generic_arg {
                    res.insert(ty_.to_owned());
                }
            });
        }
    }
    res
}

pub fn u8_slice_type() -> clean::Type {
    clean::Type::BorrowedRef {
        lifetime: None,
        mutability: Mutability::Not,
        type_: Box::new(clean::Type::Slice(Box::new(clean::Type::Primitive(
            clean::PrimitiveType::U8,
        )))),
    }
}

pub fn str_type() -> clean::Type {
    clean::Type::BorrowedRef {
        lifetime: None,
        mutability: Mutability::Not,
        type_: Box::new(clean::Type::Primitive(clean::PrimitiveType::Str)),
    }
}

pub fn i32_type() -> clean::Type {
    clean::Type::Primitive(clean::PrimitiveType::I32)
}

pub fn u8_type() -> clean::Type {
    clean::Type::Primitive(clean::PrimitiveType::U8)
}

pub fn usize_type() -> clean::Type {
    clean::Type::Primitive(clean::PrimitiveType::Usize)
}

pub fn mutable_u8_slice_type() -> clean::Type {
    clean::Type::BorrowedRef {
        lifetime: None,
        mutability: Mutability::Mut,
        type_: Box::new(clean::Type::Slice(Box::new(u8_type()))),
    }
}
