#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function2(_param0 :()) {
    let _: axum_core::response::ErrorResponse = <axum_core::response::ErrorResponse as std::convert::From::<()>>::from(_param0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = ();
        test_function2(_param0);
    });
}
