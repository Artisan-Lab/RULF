#![feature(inline_const)]

struct S<'a>(&'a u8);
fn foo() {}

// Paren generic args in AnonConst
fn a() -> [u8; foo::()] {
//~^ ERROR parenthesized type parameters may only be used with a `Fn` trait
//~| ERROR mismatched types
    panic!()
}

// Paren generic args in ConstGeneric
fn b<const C: u8()>() {}
//~^ ERROR parenthesized type parameters may only be used with a `Fn` trait

// Paren generic args in AnonymousReportError
fn c<T = u8()>() {}
//~^ ERROR parenthesized type parameters may only be used with a `Fn` trait
//~| ERROR defaults for type parameters are only allowed in
//~| WARN this was previously accepted

// Elided lifetime in path in ConstGeneric
fn d<const C: S>() {}
//~^ ERROR missing lifetime specifier
//~| ERROR `S<'static>` is forbidden as the type of a const generic parameter

fn main() {}
