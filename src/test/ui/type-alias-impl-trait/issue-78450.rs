// check-pass

#![feature(type_alias_impl_trait)]

pub trait AssociatedImpl {
    type ImplTrait;

    fn f() -> Self::ImplTrait;
}

struct S<T>(T);

trait Associated {
    type A;
}

impl<'a, T: Associated<A = &'a ()>> AssociatedImpl for S<T> {
    type ImplTrait = impl core::fmt::Debug;

    fn f() -> Self::ImplTrait {
        ()
    }
}

fn main() {}
