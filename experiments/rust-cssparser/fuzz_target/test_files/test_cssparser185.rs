#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect("slice with incorrect length");
    f32::from_le_bytes(data_array)
}

fn test_function185(_param0 :f32) {
    let _local0_param0_helper1 = &(_param0);
    let _local0 = <f32 as cssparser::ToCss>::to_css_string(_local0_param0_helper1);
    let _local1 = <cssparser::CowRcStr::<'_> as std::default::Default>::default();
    let _local2_param0_helper1 = &(_local1);
    let _local2_param1_helper1 = &(_local0);
    let _: std::option::Option::<std::cmp::Ordering> = <cssparser::CowRcStr::<'_> as std::cmp::PartialOrd::<std::string::String>>::partial_cmp(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_f32(data, 0);
        test_function185(_param0);
    });
}
