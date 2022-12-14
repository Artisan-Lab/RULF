// run-pass (note: this is spec-UB, but it works for now)
// ignore-32bit (needs `usize` to be 8-aligned to reproduce all the errors below)
#![allow(dead_code)]
// ignore-emscripten weird assertion?

#[repr(C, packed(4))]
struct Foo4C {
    bar: u8,
    baz: usize
}

#[warn(unaligned_references)]
pub fn main() {
    let foo = Foo4C { bar: 1, baz: 2 };
    let brw = &foo.baz; //~WARN reference to packed field is unaligned
    //~^ previously accepted
    assert_eq!(*brw, 2);
}
