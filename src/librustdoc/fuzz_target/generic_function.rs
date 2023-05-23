use crate::clean::Type;
use crate::clean::{self, GenericBound, WherePredicate};
use crate::clean::{GenericParamDefKind, Generics};
use crate::formats::cache::Cache;
use crate::fuzz_target::def_set::DefSet;
use crate::fuzz_target::{api_function::ApiFunction, api_util, impl_util::FullNameMap};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_span::symbol::Symbol;

pub(crate) fn analyse_generics(generics: &Generics) -> FxHashMap<String, DefSet> {
    let mut res = FxHashMap::default();
    for param in generics.params.iter() {
        match &param.kind {
            GenericParamDefKind::Type { did, bounds, .. } => {
                res.insert(param.name.to_string(), bounds_to_facts(bounds));
            }
            GenericParamDefKind::Const { .. } => {
                println!("unsupport generic (const)");
            }
            GenericParamDefKind::Lifetime { .. } => {
                println!("unsupport generic (lifetime)");
            }
        }
    }
    for param in generics.where_predicates.iter() {
        match param {
            WherePredicate::BoundPredicate { ty, bounds, bound_params } => {
                if let Type::Generic(sym) = ty {
                    res.insert(sym.to_string(), bounds_to_facts(&bounds));
                } else {
                    unreachable!();
                }
            }
            WherePredicate::RegionPredicate { lifetime, bounds } => {
                println!("unsupport generic (RegionPredicate)");
            }
            WherePredicate::EqPredicate { lhs, rhs, bound_params } => {
                println!("unsupport generic (EqPredicate)");
            }
        }
    }
    res
}

pub(crate) fn bounds_to_facts(bounds: &[GenericBound]) -> DefSet {
    let mut res = DefSet::new();
    for bound in bounds.iter() {
        match bound {
            GenericBound::TraitBound(poly, _) => {
                // FIXME: we currenly don't consider nested generic params e.g. Trait<Trait<T>>
                res.insert(poly.trait_.def_id());
            }
            GenericBound::Outlives(lifetime) => {
                println!("bounds to facts ignore lifetime: {:?}", lifetime);
            }
        }
    }
    res
}

//impl From<FxHashSet<Def>>
#[derive(Clone)]
pub(crate) struct GenericFunction {
    pub(crate) api_function: ApiFunction,
    pub(crate) generic_params: FxHashMap<String, DefSet>, // symbol => {trait_def_id}
    pub(crate) generic_symbols: FxHashSet<String>,
    impl_count: i32, // number of impl declaration
}

impl From<ApiFunction> for GenericFunction {
    fn from(api_function: ApiFunction) -> Self {
        let mut gf = GenericFunction {
            api_function,
            generic_params: FxHashMap::default(),
            generic_symbols: FxHashSet::default(),
            impl_count: 0,
        };
        gf.resolve_argument_type();
        gf
    }
}

impl GenericFunction {
    pub(crate) fn pretty_print(&self, full_name_map: &FullNameMap, cache: &Cache) {
        let mut signature = String::from("[G]fn ");
        let mut inputs = Vec::<String>::new();
        signature.push_str(&self.api_function.full_name);
        for ty in self.api_function.inputs.iter() {
            inputs.push(api_util::_type_name(ty));
        }
        signature.push_str("(");
        signature.push_str(inputs.join(", ").as_str());
        signature.push_str(") -> ");
        if let Some(ref ty) = self.api_function.output {
            signature.push_str(api_util::_type_name(ty).as_str());
        } else {
            signature.push_str("void");
        }
        println!("{}", signature);
        print!("where: ");
        for (name, fact) in self.generic_params.iter() {
            print!("{}: {:?}, ", name, fact);
        }
        print!("\n");
        /* println!("=====\n");
        println!("{:?}\n",self.api_function.inputs);
        println!("{:?}\n",self.api_function.output);
        println!("=====\n"); */
    }

    pub fn add_generics(&mut self, generics: &Generics) {
        for param in generics.params.iter() {
            match &param.kind {
                GenericParamDefKind::Type { did, bounds, .. } => {
                    self.generic_params.insert(param.name.to_string(), bounds_to_facts(bounds));
                }
                GenericParamDefKind::Const { .. } => {
                    println!("unsupport generic (const)");
                }
                GenericParamDefKind::Lifetime { .. } => {
                    println!("unsupport generic (lifetime)");
                }
            }
        }
        for param in generics.where_predicates.iter() {
            match param {
                WherePredicate::BoundPredicate { ty, bounds, bound_params } => {
                    if let Type::Generic(sym) = ty {
                        self.generic_params.insert(sym.to_string(), bounds_to_facts(&bounds));
                    } else {
                        unreachable!();
                    }
                }
                WherePredicate::RegionPredicate { lifetime, bounds } => {
                    println!("unsupport generic (RegionPredicate)");
                }
                WherePredicate::EqPredicate { lhs, rhs, bound_params } => {
                    println!("unsupport generic (EqPredicate)");
                }
            }
        }
    }

    fn resolve_argument_type(&mut self) {
        self.resolve_impl_trait();
    }

    fn resolve_impl_trait(&mut self) {
        let mut input_vec = self.api_function.inputs.clone();
        println!("before replace: {:?}\n", input_vec);
        for type_ in &mut input_vec {
            *type_ = self.replace_impl(type_);
        }
        println!("after replace: {:?}\n", input_vec);
        self.api_function.inputs = input_vec;
        let output_type = self.api_function.output.clone();
        if let Some(type_) = output_type {
            self.api_function.output = Some(self.replace_impl(&type_));
        }
    }

    fn add_new_impl_generic(&mut self, bounds: &[GenericBound]) -> String {
        let generic_param_name = format!("impl{}", self.impl_count);
        self.impl_count += 1;
        self.generic_params.insert(generic_param_name.clone(), bounds_to_facts(bounds));
        self.generic_symbols.insert(generic_param_name.clone());
        generic_param_name
    }

    pub(crate) fn replace_impl(&mut self, ty: &clean::Type) -> clean::Type {
        if let Type::ImplTrait(bounds) = ty {
            let sym = self.add_new_impl_generic(&bounds);
            Type::Generic(Symbol::intern(&sym))
        } else if let Type::Generic(sym) = ty {
            self.generic_symbols.insert(sym.to_string());
            ty.clone()
        } else {
            let mut new_ty = ty.clone();
            // If we meet nested type, travel all type
            match new_ty {
                clean::Type::Path { ref mut path } => {
                    for segment in path.segments.iter_mut() {
                        match segment.args {
                            clean::GenericArgs::AngleBracketed { ref mut args, .. } => {
                                for generic_arg in args.iter_mut() {
                                    if let clean::GenericArg::Type(ref mut inner_ty) = generic_arg {
                                        *inner_ty = self.replace_impl(inner_ty);
                                    }
                                }
                            }
                            clean::GenericArgs::Parenthesized {
                                ref mut inputs,
                                ref mut output,
                            } => {
                                for input_ty in inputs.iter_mut() {
                                    *input_ty = self.replace_impl(input_ty);
                                }
                                if let Some(output_ty) = output {
                                    **output_ty = self.replace_impl(&output_ty);
                                }
                            }
                        }
                    }
                }
                clean::Type::Tuple(ref mut types) => {
                    for ty_ in types {
                        *ty_ = self.replace_impl(ty_);
                    }
                }
                clean::Type::Slice(ref mut type_)
                | clean::Type::Array(ref mut type_, ..)
                | clean::Type::RawPointer(_, ref mut type_)
                | clean::Type::BorrowedRef { ref mut type_, .. } => {
                    *type_ = Box::new(self.replace_impl(type_));
                }
                _ => {}
            }
            new_ty
        }
    }
}
