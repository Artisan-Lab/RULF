#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function15(_param0 :dlopen::raw::AddressInfoObtainer ,_param1 :()) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1) as *const ();
    let _ = dlopen::raw::AddressInfoObtainer::obtain(_local0_param0_helper1, _local0_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = dlopen::raw::AddressInfoObtainer{};
        let _param1 = ();
        test_function15(_param0 ,_param1);
    });
}
