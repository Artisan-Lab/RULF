use std::collections::HashSet;

use crate::clean;

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
