#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function187(_param0 :u8) {
    let _local0_param0_helper1 = &(_param0);
    let _local0 = <u8 as cssparser::ToCss>::to_css_string(_local0_param0_helper1);
    let _local1 = <cssparser::CowRcStr::<'_> as std::default::Default>::default();
    let _local2_param0_helper1 = &(_local1);
    let _local2_param1_helper1 = &(_local0);
    let _: std::option::Option::<std::cmp::Ordering> = <cssparser::CowRcStr::<'_> as std::cmp::PartialOrd::<std::string::String>>::partial_cmp(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function187(_param0);
    });
}
