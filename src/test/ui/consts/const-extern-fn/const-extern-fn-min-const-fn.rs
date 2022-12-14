#![feature(const_extern_fn)]

const extern "C" fn unsize(x: &[u8; 3]) -> &[u8] { x }
const unsafe extern "C" fn closure() -> fn() { || {} }
const unsafe extern "C" fn use_float() { 1.0 + 1.0; }
//~^ ERROR floating point arithmetic
const extern "C" fn ptr_cast(val: *const u8) { val as usize; }
//~^ ERROR pointers cannot be cast to integers


fn main() {}
