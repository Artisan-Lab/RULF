// build-fail
// compile-flags: -C debug-assertions

#![deny(arithmetic_overflow)]

fn main() {
    let _x = 1 << -1;
    //~^ ERROR: this arithmetic operation will overflow
}
