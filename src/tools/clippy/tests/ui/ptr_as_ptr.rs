// run-rustfix
// aux-build:macro_rules.rs

#![warn(clippy::ptr_as_ptr)]
#![feature(custom_inner_attributes)]

extern crate macro_rules;

macro_rules! cast_it {
    ($ptr: ident) => {
        $ptr as *const i32
    };
}

fn main() {
    let ptr: *const u32 = &42_u32;
    let mut_ptr: *mut u32 = &mut 42_u32;

    let _ = ptr as *const i32;
    let _ = mut_ptr as *mut i32;

    // Make sure the lint can handle the difference in their operator precedences.
    unsafe {
        let ptr_ptr: *const *const u32 = &ptr;
        let _ = *ptr_ptr as *const i32;
    }

    // Changes in mutability. Do not lint this.
    let _ = ptr as *mut i32;
    let _ = mut_ptr as *const i32;

    // `pointer::cast` cannot perform unsized coercions unlike `as`. Do not lint this.
    let ptr_of_array: *const [u32; 4] = &[1, 2, 3, 4];
    let _ = ptr_of_array as *const [u32];
    let _ = ptr_of_array as *const dyn std::fmt::Debug;

    // Ensure the lint doesn't produce unnecessary turbofish for inferred types.
    let _: *const i32 = ptr as *const _;
    let _: *mut i32 = mut_ptr as _;

    // Make sure the lint is triggered inside a macro
    let _ = cast_it!(ptr);

    // Do not lint inside macros from external crates
    let _ = macro_rules::ptr_as_ptr_cast!(ptr);
}

fn _msrv_1_37() {
    #![clippy::msrv = "1.37"]
    let ptr: *const u32 = &42_u32;
    let mut_ptr: *mut u32 = &mut 42_u32;

    // `pointer::cast` was stabilized in 1.38. Do not lint this
    let _ = ptr as *const i32;
    let _ = mut_ptr as *mut i32;
}

fn _msrv_1_38() {
    #![clippy::msrv = "1.38"]
    let ptr: *const u32 = &42_u32;
    let mut_ptr: *mut u32 = &mut 42_u32;

    let _ = ptr as *const i32;
    let _ = mut_ptr as *mut i32;
}
