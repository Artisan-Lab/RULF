#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function102(_param0 :i8 ,_param1 :i16) {
    let _local0_param0_helper1 = &(_param0);
    let mut _local0 = <i8 as cssparser::ToCss>::to_css_string(_local0_param0_helper1);
    let _local1_param0_helper1 = &(_param1);
    let _local1_param1_helper1 = &mut (_local0);
    let _: std::fmt::Result = <i16 as cssparser::ToCss>::to_css(_local1_param0_helper1, _local1_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 3 {return;}
        let _param0 = _to_i8(data, 0);
        let _param1 = _to_i16(data, 1);
        test_function102(_param0 ,_param1);
    });
}
