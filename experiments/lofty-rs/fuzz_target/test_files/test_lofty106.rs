#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _unwrap_option<T>(_opt: Option<T>) -> T {
    match _opt {
        Some(_t) => _t,
        None => {
            use std::process;
            process::exit(0);
        }
    }
}

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function106(_param0 :u8) {
    let _local0 = lofty::musepack::sv7::Profile::from_u8(_param0);
    let _local1 = <lofty::musepack::sv7::Profile as std::default::Default>::default();
    let _local2_param0_helper1 = _unwrap_option(_local0);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2_param1_helper1 = &(_local1);
    let _ = <lofty::musepack::sv7::Profile as std::cmp::PartialEq::<lofty::musepack::sv7::Profile>>::eq(_local2_param0_helper2, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function106(_param0);
    });
}
