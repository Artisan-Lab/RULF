#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function199(_param0 :i32) {
    let _local0 = <cssparser::CowRcStr::<'_> as std::default::Default>::default();
    let _local1_param0_helper1 = &(_param0);
    let _local1 = <i32 as cssparser::ToCss>::to_css_string(_local1_param0_helper1);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _: bool = <cssparser::CowRcStr::<'_> as std::cmp::PartialEq::<std::string::String>>::eq(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_i32(data, 0);
        test_function199(_param0);
    });
}
