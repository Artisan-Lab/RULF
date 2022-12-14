fn process_slice(data: &[i32]) {
    //~^ NOTE required by a bound in this
    //~| NOTE required by a bound in this
    todo!()
}

fn main() {
    let some_generated_vec = (0..10).collect();
    //~^ ERROR the size for values of type `[i32]` cannot be known at compilation time
    //~| ERROR the size for values of type `[i32]` cannot be known at compilation time
    //~| ERROR a slice of type `[i32]` cannot be built since `[i32]` has no definite size
    //~| NOTE try explicitly collecting into a `Vec<{integer}>`
    //~| NOTE required by a bound in `collect`
    //~| NOTE required by a bound in `collect`
    //~| NOTE all local variables must have a statically known size
    //~| NOTE doesn't have a size known at compile-time
    //~| NOTE doesn't have a size known at compile-time
    //~| NOTE required by a bound introduced by this call
    process_slice(&some_generated_vec);
}
