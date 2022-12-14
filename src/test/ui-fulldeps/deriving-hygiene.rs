// run-pass

#![allow(non_upper_case_globals)]
#![feature(rustc_private)]
extern crate rustc_macros;
extern crate rustc_serialize;

use rustc_macros::{Decodable, Encodable};

pub const other: u8 = 1;
pub const f: u8 = 1;
pub const d: u8 = 1;
pub const s: u8 = 1;
pub const state: u8 = 1;
pub const cmp: u8 = 1;

#[derive(Ord, Eq, PartialOrd, PartialEq, Debug, Decodable, Encodable, Hash)]
struct Foo {}

fn main() {}
