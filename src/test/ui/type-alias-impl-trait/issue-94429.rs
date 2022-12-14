#![feature(type_alias_impl_trait, generator_trait, generators)]
use std::ops::Generator;

trait Runnable {
    type Gen: Generator<Yield = (), Return = ()>;

    fn run(&mut self) -> Self::Gen;
}

struct Implementor {}

impl Runnable for Implementor {
    type Gen = impl Generator<Yield = (), Return = ()>;

    fn run(&mut self) -> Self::Gen {
    //~^ ERROR: type mismatch resolving
        move || {
            yield 1;
        }
    }
}

fn main() {}
