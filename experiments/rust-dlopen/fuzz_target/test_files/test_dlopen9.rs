#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function9(_param0 :dlopen::raw::AddressInfoObtainer) {
    let _local0_param0_helper1 = &(_param0) as *const dlopen::raw::AddressInfoObtainer;
    let _local0: dlopen::symbor::Symbol::<'_, *const dlopen::raw::AddressInfoObtainer> = dlopen::symbor::Symbol::<'_, *const dlopen::raw::AddressInfoObtainer>::new(_local0_param0_helper1);
    let _local1_param0_helper1 = &(_local0);
    let _: &*const dlopen::raw::AddressInfoObtainer = <dlopen::symbor::Symbol::<'_, *const dlopen::raw::AddressInfoObtainer> as std::ops::Deref>::deref(_local1_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = dlopen::raw::AddressInfoObtainer{};
        test_function9(_param0);
    });
}
