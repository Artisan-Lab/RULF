#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect("slice with incorrect length");
    f32::from_le_bytes(data_array)
}

fn test_function106(_param0 :u16 ,_param1 :f32 ,_param2 :bool) {
    let _local0_param0_helper1 = &(_param0);
    let mut _local0 = <u16 as cssparser::ToCss>::to_css_string(_local0_param0_helper1);
    let _local1_param0_helper1 = &mut (_local0);
    let _local1_param1_helper1 = Some(_param1);
    let _: std::fmt::Result = cssparser::color::serialize_color_alpha(_local1_param0_helper1, _local1_param1_helper1, _param2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 7 {return;}
        let _param0 = _to_u16(data, 0);
        let _param1 = _to_f32(data, 2);
        let _param2 = _to_bool(data, 6);
        test_function106(_param0 ,_param1 ,_param2);
    });
}
