use std::collections::HashMap;

use crate::clean;

use super::api_function::ApiFunction;

#[derive(Clone)]
pub(crate) struct GenericFunction<'a> {
    pub(crate) api_function: ApiFunction<'a>,
    pub(crate) generic_substitute: HashMap<String, clean::Type>,
}

impl<'a> From<ApiFunction<'a>> for GenericFunction<'a> {
    fn from(api_function: ApiFunction<'a>) -> Self {
        GenericFunction { api_function, generic_substitute: HashMap::new() }
    }
}
