#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _unwrap_result<T, E>(_res: Result<T, E>) -> T {
    match _res {
        Ok(_t) => _t,
        Err(_) => {
            use std::process;
            process::exit(0);
        },
    }
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function13(mut _param0 :&[u8] ,mut _param1 :&[u8]) {
    let _local0_param0_helper1 = &mut (_param0);
    let _local0: std::result::Result::<odoh_rs::ObliviousDoHMessagePlaintext, odoh_rs::Error> = <odoh_rs::ObliviousDoHMessagePlaintext as odoh_rs::Deserialize>::deserialize(_local0_param0_helper1);
    let _local1_param0_helper1 = &mut (_param1);
    let _local1: std::result::Result::<odoh_rs::ObliviousDoHMessagePlaintext, odoh_rs::Error> = <odoh_rs::ObliviousDoHMessagePlaintext as odoh_rs::Deserialize>::deserialize(_local1_param0_helper1);
    let _local2_param0_helper1 = _unwrap_result(_local0);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2_param1_helper1 = _unwrap_result(_local1);
    let _local2_param1_helper2 = &(_local2_param1_helper1);
    let _ = <odoh_rs::ObliviousDoHMessagePlaintext as std::cmp::PartialEq::<odoh_rs::ObliviousDoHMessagePlaintext>>::eq(_local2_param0_helper2, _local2_param1_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 0) / 2;
        let _param0 = _to_slice::<u8>(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param1 = _to_slice::<u8>(data, 0 + 1 * dynamic_length, data.len());
        test_function13(_param0 ,_param1);
    });
}
