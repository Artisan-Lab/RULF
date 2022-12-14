// This test check that we correctly emit an warning for compact cfg
//
// check-pass
// compile-flags:--check-cfg=values() -Z unstable-options

#![feature(cfg_target_compact)]

#[cfg(target(os = "linux", arch = "arm"))]
pub fn expected() {}

#[cfg(target(os = "linux", arch = "X"))]
//~^ WARNING unexpected `cfg` condition value
pub fn unexpected() {}

fn main() {}
