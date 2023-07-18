use crate::clean::types::QPathData;
use crate::clean::Path;
use crate::clean::PrimitiveType;
use crate::clean::Type;
use crate::clean::Visibility;
use crate::formats::cache::Cache;
use crate::fuzz_target::api_function::ApiFunction;
use crate::fuzz_target::api_sequence::{ApiCall, ApiSequence, ParamType};
use crate::fuzz_target::api_util;
use crate::fuzz_target::api_util::_type_name;
use crate::fuzz_target::call_type::CallType;
use crate::fuzz_target::fuzz_target_renderer::FuzzTargetContext;
use crate::fuzz_target::fuzzable_type;
use crate::fuzz_target::fuzzable_type::FuzzableType;
use crate::fuzz_target::generic_function;
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::generic_param_map::GenericParamMap;
use crate::fuzz_target::generic_solver::GenericSolver;
use crate::fuzz_target::impl_util::FullNameMap;
use crate::fuzz_target::mod_visibility::ModVisibity;
use crate::fuzz_target::prelude_type;
use crate::fuzz_target::statistic;
use crate::html::format::join_with_double_colon;
use crate::TyCtxt;
use lazy_static::lazy_static;
use rand::{self, Rng};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::cmp::{max, min};
use std::{cell::RefCell, rc::Rc};

pub(crate) struct TraitImpl {
    pub(crate) trait_: Path,
    pub(crate) for_: Type,
    pub(crate) generic_map: GenericParamMap,
    pub(crate) impl_id: DefId,
    pub(crate) assoc_items: Vec<(QPathData, Type)>,
}

impl TraitImpl {
    pub(crate) fn new(trait_: Path, for_:Type, generic_map: GenericParamMap, impl_id: DefId) -> TraitImpl {
        TraitImpl { trait_, for_, impl_id, generic_map, assoc_items: Vec::new() }
    }
}
