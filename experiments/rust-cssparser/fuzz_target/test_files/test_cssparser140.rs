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

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
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

fn test_function140(_param0 :i16 ,_param1 :u32) {
    let _local0_param0_helper1 = &(_param0);
    let mut _local0 = <i16 as cssparser::ToCss>::to_css_string(_local0_param0_helper1);
    let _local1_param0_helper1 = &(_param1);
    let _local1_param1_helper1 = &mut (_local0);
    let _: std::fmt::Result = <u32 as cssparser::ToCss>::to_css(_local1_param0_helper1, _local1_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 6 {return;}
        let _param0 = _to_i16(data, 0);
        let _param1 = _to_u32(data, 2);
        test_function140(_param0 ,_param1);
    });
}
