#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function12(_param0 :dlopen::raw::AddressInfoObtainer) {
    let _local0_param0_helper1 = &(_param0) as *const dlopen::raw::AddressInfoObtainer;
    let mut _local0: dlopen::symbor::Symbol::<'_, *const dlopen::raw::AddressInfoObtainer> = dlopen::symbor::Symbol::<'_, *const dlopen::raw::AddressInfoObtainer>::new(_local0_param0_helper1);
    let _local1_param0_helper1 = &mut (_local0);
    let _: &mut *const dlopen::raw::AddressInfoObtainer = <dlopen::symbor::Symbol::<'_, *const dlopen::raw::AddressInfoObtainer> as std::ops::DerefMut>::deref_mut(_local1_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = dlopen::raw::AddressInfoObtainer{};
        test_function12(_param0);
    });
}
