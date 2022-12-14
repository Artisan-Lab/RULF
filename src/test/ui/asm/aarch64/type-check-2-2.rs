// only-aarch64

#![feature(repr_simd, never_type)]

use std::arch::{asm, global_asm};

#[repr(simd)]
#[derive(Clone, Copy)]
struct SimdType(f32, f32, f32, f32);

#[repr(simd)]
struct SimdNonCopy(f32, f32, f32, f32);

fn main() {
    unsafe {
        // Inputs must be initialized

        let x: u64;
        asm!("{}", in(reg) x);
        //~^ ERROR used binding `x` isn't initialized
        let mut y: u64;
        asm!("{}", inout(reg) y);
        //~^ ERROR used binding `y` isn't initialized
        let _ = y;

        // Outputs require mutable places

        let v: Vec<u64> = vec![0, 1, 2];
        asm!("{}", in(reg) v[0]);
        asm!("{}", out(reg) v[0]);
        //~^ ERROR cannot borrow `v` as mutable, as it is not declared as mutable
        asm!("{}", inout(reg) v[0]);
        //~^ ERROR cannot borrow `v` as mutable, as it is not declared as mutable

        // Sym operands must point to a function or static
    }
}
