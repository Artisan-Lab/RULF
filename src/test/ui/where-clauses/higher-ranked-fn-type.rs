// revisions: quiet verbose
// [verbose]compile-flags: -Zverbose

#![allow(unused_parens)]

trait Foo {
    type Assoc;
}

fn called()
where
    for<'b> fn(&'b ()): Foo,
{
}

fn caller()
where
    (for<'a> fn(&'a ())): Foo,
{
    called()
    //[quiet]~^ ERROR the trait bound `for<'b> fn(&'b ()): Foo` is not satisfied
    //[verbose]~^^ ERROR the trait bound `for<'b> fn(&ReLateBound(
}

fn main() {}
