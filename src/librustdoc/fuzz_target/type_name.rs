use itertools::Itertools;
use rustc_hir::def_id::DefId;
use std::collections::HashMap;

use crate::clean::{self, GenericArg, GenericBound, GetDefId, Lifetime, Path, TypeBinding};
use crate::html::render::cache::Cache;
use rustc_hir::Mutability;

use super::prelude_type::is_preluded_type_name;

lazy_static! {
    static ref PRELUDED_TYPE_NAME: HashMap<&'static str, &'static str> = {
        let mut m = HashMap::new();
        m.insert("core::option::Option", "Option");
        m.insert("core::result::Result", "Result");
        m.insert("alloc::string::String", "String");
        m.insert("alloc::vec::Vec", "Vec");
        m.insert("alloc::boxed::Box", "Box");
        m
    };
}

/// 类型名的种类
#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum TypeNameKind {
    // 定义在当前库的类型
    Type,
    // 定义在当前库的trait
    Trait,
    // 定义在外部库的类型
    ExternType,
    // 定义在外部库的trait
    ExternTrait,
    // 预先引入的类型
    Prelude,
}

/// define level to get type/trait name
#[derive(Debug, Clone, Hash, Copy, PartialEq, Eq)]
pub enum TypeNameLevel {
    // type/trait defined in current crate
    _Crate,
    // type/trait defined in current crate or prelude
    _Prelude,
    // all types/traits
    All,
}

impl TypeNameLevel {
    fn type_kinds(&self) -> Vec<TypeNameKind> {
        match self {
            TypeNameLevel::_Crate => vec![TypeNameKind::Type, TypeNameKind::Trait],
            TypeNameLevel::_Prelude => {
                vec![TypeNameKind::Type, TypeNameKind::Trait, TypeNameKind::Prelude]
            }
            TypeNameLevel::All => vec![
                TypeNameKind::Type,
                TypeNameKind::Trait,
                TypeNameKind::Prelude,
                TypeNameKind::ExternType,
                TypeNameKind::ExternTrait,
            ],
        }
    }
}

/// map def_id to full-qulified type_name
#[derive(Debug, Clone)]
pub struct TypeNameMap {
    pub map: HashMap<DefId, (String, TypeNameKind)>,
}

impl TypeNameMap {
    pub fn new() -> Self {
        TypeNameMap { map: HashMap::new() }
    }

    fn insert(&mut self, def_id: DefId, type_name: String, type_kind: TypeNameKind) {
        self.map.insert(def_id, (type_name, type_kind));
    }

    fn get_type_name(&self, def_id: &DefId, type_name_level: TypeNameLevel) -> Option<String> {
        // Some type may does not have type name, we will return unknown types.
        // e.g., indices
        let (type_name, type_name_kind) = if self.map.contains_key(def_id) {
            self.map.get(def_id).unwrap()
        } else {
            return None;
        };
        let valid_type_kinds = type_name_level.type_kinds();
        if valid_type_kinds.contains(type_name_kind) { Some(type_name.to_owned()) } else { None }
    }
}

impl From<&Cache> for TypeNameMap {
    fn from(cache: &Cache) -> TypeNameMap {
        let mut type_name_map = TypeNameMap::new();
        // path defined in current crate
        cache.paths.iter().for_each(|(def_id, (segments, _))| {
            let type_name = full_qualified_name(segments);
            if cache.traits.contains_key(def_id) {
                // trait defined in current crate
                type_name_map.insert(*def_id, type_name, TypeNameKind::Trait)
            } else {
                // type defined in current crate
                type_name_map.insert(*def_id, type_name, TypeNameKind::Type)
            }
        });
        // paths defined in external crates
        cache.external_paths.iter().for_each(|(def_id, (segments, _))| {
            let type_name = full_qualified_name(segments);
            if is_preluded_type_name(&type_name) {
                // prelude type only defines in external crate
                type_name_map.insert(*def_id, type_name, TypeNameKind::Prelude)
            } else if cache.traits.contains_key(def_id) {
                // trait defined in external crate
                type_name_map.insert(*def_id, type_name, TypeNameKind::ExternTrait)
            } else {
                // type defined in external crate
                type_name_map.insert(*def_id, type_name, TypeNameKind::ExternType)
            }
        });
        type_name_map
    }
}

/// Get the full name of type.
/// The main difference between type_name and type_full_name is that
/// type_full_name will also try to get names of all type parameters, while type_name only get the current type name.
/// FIXME：We will lose keyword `dyn` of trait object; We skip all lifetime parameters.
pub fn type_full_name(
    type_: &clean::Type,
    type_name_map: &TypeNameMap,
    type_name_level: TypeNameLevel,
) -> String {
    let type_name = match type_ {
        clean::Type::ResolvedPath { path, did, .. } => {
            let type_name =
                if let Some(type_name) = type_name_map.get_type_name(did, type_name_level) {
                    type_name
                } else {
                    // println!("Warning: try to get type full name for {:?}", type_);
                    return "Unknown type".to_string();
                };
            let striped_type_name = strip_prelude_type_name(&type_name);
            let type_parameter_name =
                type_parameters_full_name(path, type_name_map, type_name_level);
            format!("{}{}", striped_type_name, type_parameter_name)
        }
        clean::Type::Tuple(types) => {
            let type_full_names = types
                .iter()
                .map(|ty| type_full_name(ty, type_name_map, type_name_level))
                .collect_vec();
            format!("({})", type_full_names.join(","))
        }
        clean::Type::Slice(ty) => {
            format!("[{}]", type_full_name(&**ty, type_name_map, type_name_level))
        }
        clean::Type::Array(ty, len) => {
            format!("[{};{}]", type_full_name(&**ty, type_name_map, type_name_level), len)
        }
        clean::Type::RawPointer(mutability, ty) => {
            let modifier = raw_pointer_modifier(mutability);
            format!("*{}{}", modifier, type_full_name(&**ty, type_name_map, type_name_level))
        }
        clean::Type::BorrowedRef { lifetime, mutability, type_ } => {
            let lifetime = lifetime_name(lifetime);
            let modifier = borrowed_ref_modifier(mutability);
            format!(
                "&{}{}{}",
                lifetime,
                modifier,
                type_full_name(type_, type_name_map, type_name_level)
            )
        }
        clean::Type::QPath { name, self_type, trait_ } => {
            format!(
                "<{} as {}>::{}",
                type_full_name(&**self_type, type_name_map, type_name_level),
                type_full_name(&**trait_, type_name_map, type_name_level),
                name
            )
        }
        clean::Type::ImplTrait(generic_bounds) => {
            let traits = generic_bounds
                .iter()
                .map(|generic_bound| {
                    generic_bound_full_name(generic_bound, type_name_map, type_name_level)
                })
                .collect_vec();
            format!("impl {}", traits.join("+"))
        }
        _ => type_name(type_, type_name_map, type_name_level),
    };
    strip_prelude_type_name(&type_name)
}

pub fn type_name(
    type_: &clean::Type,
    type_name_map: &TypeNameMap,
    type_name_level: TypeNameLevel,
) -> String {
    let type_name = match type_ {
        clean::Type::ResolvedPath { did, .. } => {
            if let Some(type_name) = type_name_map.get_type_name(did, type_name_level) {
                return type_name;
            } else {
                // println!("Warning: try to get type name for {:?}", type_);
                return "Unknown type".to_string();
            };
        }
        clean::Type::Generic(generic_name) => generic_name.to_owned(),
        clean::Type::Primitive(primitive_type) => primitive_type.as_str().to_string(),
        clean::Type::Tuple(types) => {
            let type_names =
                types.iter().map(|ty| type_name(ty, type_name_map, type_name_level)).collect_vec();
            format!("({})", type_names.join(","))
        }
        clean::Type::Slice(ty) => format!("[{}]", type_name(&**ty, type_name_map, type_name_level)),
        clean::Type::Array(ty, len) => {
            format!("[{};{}]", type_name(&**ty, type_name_map, type_name_level), len)
        }
        clean::Type::Never => "!".to_string(),
        clean::Type::RawPointer(mutability, ty) => {
            let modifier = raw_pointer_modifier(mutability);
            format!("*{}{}", modifier, type_name(&**ty, type_name_map, type_name_level))
        }
        clean::Type::BorrowedRef { lifetime, mutability, type_ } => {
            let lifetime = lifetime_name(lifetime);
            let modifier = borrowed_ref_modifier(mutability);
            format!("&{}{}{}", lifetime, modifier, type_name(type_, type_name_map, type_name_level))
        }
        clean::Type::QPath { name, self_type, trait_ } => {
            format!(
                "<{} as {}>::{}",
                type_name(&**self_type, type_name_map, type_name_level),
                type_name(&**trait_, type_name_map, type_name_level),
                name
            )
        }
        clean::Type::Infer => "_".to_string(),
        clean::Type::ImplTrait(generic_bounds) => {
            let traits = generic_bounds
                .iter()
                .map(|generic_bound| {
                    generic_bound_name(generic_bound, type_name_map, type_name_level)
                })
                .collect_vec();
            format!("impl {}", traits.join("+"))
        }
        clean::Type::BareFunction(..) => {
            unreachable!("Internal Error. We won't try to get type name of these types.")
        }
    };
    strip_prelude_type_name(&type_name)
}

// pub fn _type_full_name_without_lifetime(type_: &clean::Type, type_name_map: &TypeNameMap, type_name_level: TypeNameLevel) -> String {
// }

// debug use
pub fn _type_name_with_def_id(
    type_: &clean::Type,
    type_name_map: &TypeNameMap,
    type_name_level: TypeNameLevel,
) -> String {
    let type_full_name = type_full_name(type_, type_name_map, type_name_level);
    if let Some(def_id) = type_.def_id() {
        format!("{} def_id: {:?}", type_full_name, def_id)
    } else {
        type_full_name
    }
}

fn raw_pointer_modifier(mutability: &Mutability) -> &'static str {
    match mutability {
        // 补上空格
        Mutability::Mut => "mut ",
        Mutability::Not => "const ",
    }
}

fn borrowed_ref_modifier(mutability: &Mutability) -> &'static str {
    match mutability {
        // add a space
        Mutability::Mut => "mut ",
        Mutability::Not => "",
    }
}

/// the name of lifetime(with additional space)
fn lifetime_name(lifetime: &Option<Lifetime>) -> String {
    if let Some(lifetime_) = lifetime {
        // add a space
        format!("{} ", lifetime_.get_ref())
    } else {
        "".to_string()
    }
}

pub fn generic_bound_name(
    generic_bound: &GenericBound,
    type_name_map: &TypeNameMap,
    type_name_level: TypeNameLevel,
) -> String {
    match generic_bound {
        GenericBound::TraitBound(poly_trait, ..) => {
            type_name(&poly_trait.trait_, type_name_map, type_name_level)
        }
        GenericBound::Outlives(lifetime) => lifetime.get_ref().to_string(),
    }
}

fn generic_bound_full_name(
    generic_bound: &GenericBound,
    type_name_map: &TypeNameMap,
    type_name_level: TypeNameLevel,
) -> String {
    match generic_bound {
        GenericBound::TraitBound(poly_trait, ..) => {
            type_full_name(&poly_trait.trait_, type_name_map, type_name_level)
        }
        GenericBound::Outlives(lifetime) => lifetime.get_ref().to_string(),
    }
}

// This is currently an ugly patch for serde_json
// Some type name may contains private mod, so this type name cannot be used as return type notation.
// we should special deal with such cases.
pub fn only_public_type_name(type_: &clean::Type, type_name_map: &TypeNameMap, type_name_level: TypeNameLevel) -> String {
    let type_full_name = type_full_name(type_, type_name_map, type_name_level);
    match type_full_name.as_str() {
        "serde_json::Result<std::net::ip::Ipv4Addr>" => "serde_json::Result<std::net::Ipv4Addr>".to_string(),
        _ => type_full_name
    }
}

fn type_parameters_full_name(
    path: &Path,
    type_name_map: &TypeNameMap,
    type_name_level: TypeNameLevel,
) -> String {
    let segments = &path.segments;
    let segment_names = segments
        .iter()
        .map(|path_segment| {
            // We don't need segment name, we get full name by type name
            // if path_segment.name.len() > 0 {
            //     todo!("path segment has name {}", path_segment.name);
            // }
            match path_segment.args {
                clean::GenericArgs::AngleBracketed { ref args, ref bindings } => {
                    if bindings.len() != 0 {
                        let type_bindings = bindings
                            .iter()
                            .map(|type_binding| {
                                let TypeBinding { name, kind } = type_binding;
                                match kind {
                                    clean::TypeBindingKind::Equality { ty } => {
                                        let bind_type_name =
                                            type_full_name(ty, type_name_map, type_name_level);
                                        format!("<{}={}>", name, bind_type_name)
                                    }
                                    clean::TypeBindingKind::Constraint { .. } => {
                                        todo!("deal with constraint binds.")
                                    }
                                }
                            })
                            .collect_vec()
                            .join(",");
                        if args.len() == 0 {
                            return type_bindings;
                        } else {
                            todo!("type bindings coexist with args.")
                        }
                    }

                    let arg_names =
                        args.iter()
                            .filter(|generic_arg| {
                                if let GenericArg::Type(..) = generic_arg { true } else { false }
                            })
                            .map(|generic_arg| {
                                if let GenericArg::Type(ty) = generic_arg {
                                    type_full_name(ty, type_name_map, type_name_level)
                                } else {
                                    // This line is used to pass compilation
                                    unreachable!("Internal Error. Code should not reach this arm.")
                                }
                            })
                            .collect_vec();
                    if arg_names.len() > 0 {
                        format!("<{}>", arg_names.join(","))
                    } else {
                        "".to_string()
                    }
                }
                clean::GenericArgs::Parenthesized { ref inputs, ref output } => {
                    let input_names = inputs
                        .iter()
                        .map(|input| type_full_name(input, type_name_map, type_name_level))
                        .collect_vec();
                    let output_name = output
                        .as_ref()
                        .map(|ty| type_full_name(ty, type_name_map, type_name_level));
                    if let Some(output_name) = output_name {
                        format!("({})->{}", input_names.join(","), output_name)
                    } else {
                        format!("({})", input_names.join(","))
                    }
                }
            }
        })
        .collect_vec();
    // segment_names.join("::")
    full_qualified_name(&segment_names)
}

fn strip_prelude_type_name(raw: &str) -> String {
    if PRELUDED_TYPE_NAME.contains_key(&raw) {
        PRELUDED_TYPE_NAME.get(&raw).unwrap().to_string()
    } else {
        raw.to_string()
    }
}

fn full_qualified_name(segments: &Vec<String>) -> String {
    let non_empty_segments = segments
        .iter()
        .filter(|segment| segment.len() > 0)
        .map(|segment| segment.to_owned())
        .collect_vec();
    non_empty_segments.join("::")
}

