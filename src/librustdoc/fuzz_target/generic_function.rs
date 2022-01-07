use std::collections::HashMap;

use crate::clean;

use super::api_function::ApiFunction;

#[derive(Debug, Clone)]
pub struct GenericFunction {
    pub api_function: ApiFunction,
    pub generic_substitute: HashMap<String, clean::Type>,
}

impl From<ApiFunction> for GenericFunction {
    fn from(api_function: ApiFunction) -> Self {
        GenericFunction { api_function, generic_substitute: HashMap::new() }
    }
}
