#![feature(box_patterns)]
#![feature(internal_output_capture)]
#![feature(thread_spawn_unchecked)]
#![feature(once_cell)]
#![recursion_limit = "256"]
#![allow(rustc::potential_query_instability)]
#![deny(rustc::untranslatable_diagnostic)]
#![deny(rustc::diagnostic_outside_of_impl)]

#[macro_use]
extern crate tracing;

mod callbacks;
mod errors;
pub mod interface;
mod passes;
mod proc_macro_decls;
mod queries;
pub mod util;

pub use callbacks::setup_callbacks;
pub use interface::{run_compiler, Config};
pub use passes::{DEFAULT_EXTERN_QUERY_PROVIDERS, DEFAULT_QUERY_PROVIDERS};
pub use queries::Queries;

#[cfg(test)]
mod tests;
