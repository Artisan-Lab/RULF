// edition:2018
// ignore-compare-mode-chalk

#![feature(type_alias_impl_trait)]

pub trait Bar {
    type E: Copy;

    fn foo<T>() -> Self::E;
}

impl<S> Bar for S {
    type E = impl std::marker::Copy;
    fn foo<T>() -> Self::E {
    //~^ ERROR the trait bound `impl Future<Output = ()>: Copy` is not satisfied [E0277]
        async {}
    }
}

fn main() {}
