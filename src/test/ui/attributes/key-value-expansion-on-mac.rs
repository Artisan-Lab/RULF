#![feature(rustc_attrs)]

#[rustc_dummy = stringify!(a)] // OK
macro_rules! bar {
    () => {};
}

// FIXME?: `bar` here expands before `stringify` has a chance to expand.
// `#[rustc_dummy = ...]` is validated and dropped during expansion of `bar`,
// the "unexpected expression" errors comes from the validation.
#[rustc_dummy = stringify!(b)] //~ ERROR unexpected expression: `stringify!(b)`
bar!();

fn main() {}
