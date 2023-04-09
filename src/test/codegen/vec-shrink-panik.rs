// compile-flags: -O
// ignore-debug: the debug assertions get in the way
#![crate_type = "lib"]
#![feature(shrink_to)]

// Make sure that `Vec::shrink_to_fit` never emits panics via `RawVec::shrink_to_fit`,
// "Tried to shrink to a larger capacity", because the length is *always* <= capacity.

// CHECK-LABEL: @shrink_to_fit
#[no_mangle]
pub fn shrink_to_fit(vec: &mut Vec<u32>) {
    // CHECK-NOT: panic
    vec.shrink_to_fit();
}

// CHECK-LABEL: @issue71861
#[no_mangle]
pub fn issue71861(vec: Vec<u32>) -> Box<[u32]> {
    // CHECK-NOT: panic

    // Call to panic_no_unwind in case of double-panic is expected,
    // but other panics are not.
    // CHECK: cleanup
    // CHECK-NEXT: ; call core::panicking::panic_no_unwind
    // CHECK-NEXT: panic_no_unwind

    // CHECK-NOT: panic
    vec.into_boxed_slice()
}

// CHECK-LABEL: @issue75636
#[no_mangle]
pub fn issue75636<'a>(iter: &[&'a str]) -> Box<[&'a str]> {
    // CHECK-NOT: panic

    // Call to panic_no_unwind in case of double-panic is expected,
    // but other panics are not.
    // CHECK: cleanup
    // CHECK-NEXT: ; call core::panicking::panic_no_unwind
    // CHECK-NEXT: panic_no_unwind

    // CHECK-NOT: panic
    iter.iter().copied().collect()
}

// CHECK: ; core::panicking::panic_no_unwind
// CHECK: declare void @{{.*}}panic_no_unwind
