// ignore-stage1
// compile-flags: -Zdeduplicate-diagnostics=yes
extern crate rustc_data_structures;
//~^ use of unstable library feature 'rustc_private'
extern crate rustc_macros;
//~^ use of unstable library feature 'rustc_private'
extern crate rustc_query_system;
//~^ use of unstable library feature 'rustc_private'

use rustc_macros::HashStable;
//~^ use of unstable library feature 'rustc_private'

#[derive(HashStable)]
//~^ use of unstable library feature 'rustc_private'
struct Test;

fn main() {}
