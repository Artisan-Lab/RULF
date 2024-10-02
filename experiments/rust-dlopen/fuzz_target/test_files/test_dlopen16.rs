#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function16(_param0 :dlopen::raw::AddressInfoObtainer) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param0_helper2 = &(_local0_param0_helper1) as *const &dlopen::raw::AddressInfoObtainer;
    let _: dlopen::symbor::PtrOrNull::<'_, &dlopen::raw::AddressInfoObtainer> = dlopen::symbor::PtrOrNull::<'_, &dlopen::raw::AddressInfoObtainer>::new(_local0_param0_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = dlopen::raw::AddressInfoObtainer{};
        test_function16(_param0);
    });
}
