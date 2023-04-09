#![feature(type_alias_impl_trait)]

use std::fmt::Debug;

fn main() {}

// test that unused generic parameters are ok
type TwoTys<T, U> = impl Debug;


pub trait Captures<'a> {}

impl<'a, T: ?Sized> Captures<'a> for T {}

type TwoLifetimes<'a, 'b> = impl Debug + Captures<'a> + Captures<'b>;

type TwoConsts<const X: usize, const Y: usize> = impl Debug;


fn one_ty<T: Debug>(t: T) -> TwoTys<T, T> {
    t
    //~^ ERROR non-defining opaque type use in defining scope
}

fn one_lifetime<'a>(t: &'a u32) -> TwoLifetimes<'a, 'a> {
    t
    //~^ ERROR non-defining opaque type use in defining scope
}

fn one_const<const N: usize>(t: *mut [u8; N]) -> TwoConsts<N, N> {
    t
    //~^ ERROR non-defining opaque type use in defining scope
}
