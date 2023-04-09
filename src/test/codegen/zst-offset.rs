// compile-flags: -C no-prepopulate-passes

#![crate_type = "lib"]
#![feature(repr_simd)]

// Hack to get the correct size for the length part in slices
// CHECK: @helper([[USIZE:i[0-9]+]] %_1)
#[no_mangle]
pub fn helper(_: usize) {
}

// Check that we correctly generate a GEP for a ZST that is not included in Scalar layout
// CHECK-LABEL: @scalar_layout
#[no_mangle]
pub fn scalar_layout(s: &(u64, ())) {
// CHECK: getelementptr i8, {{.+}}, [[USIZE]] 8
    let x = &s.1;
    &x; // keep variable in an alloca
}

// Check that we correctly generate a GEP for a ZST that is not included in ScalarPair layout
// CHECK-LABEL: @scalarpair_layout
#[no_mangle]
pub fn scalarpair_layout(s: &(u64, u32, ())) {
// CHECK: getelementptr i8, {{.+}}, [[USIZE]] 12
    let x = &s.2;
    &x; // keep variable in an alloca
}

#[repr(simd)]
pub struct U64x4(u64, u64, u64, u64);

// Check that we correctly generate a GEP for a ZST that is not included in Vector layout
// CHECK-LABEL: @vector_layout
#[no_mangle]
pub fn vector_layout(s: &(U64x4, ())) {
// CHECK: getelementptr i8, {{.+}}, [[USIZE]] 32
    let x = &s.1;
    &x; // keep variable in an alloca
}
