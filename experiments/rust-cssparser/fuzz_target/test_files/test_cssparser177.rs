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

fn _to_u64(data:&[u8], index:usize)->u64 {
    let data0 = _to_u32(data, index) as u64;
    let data1 = _to_u32(data, index+4) as u64;
    data0 << 32 | data1
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function177(_param0 :u64 ,_param1 :i8) {
    let _local0_param0_helper1 = &(_param0);
    let mut _local0 = <u64 as cssparser::ToCss>::to_css_string(_local0_param0_helper1);
    let _local1_param0_helper1 = &(_param1);
    let _local1_param1_helper1 = &mut (_local0);
    let _: std::fmt::Result = <i8 as cssparser::ToCss>::to_css(_local1_param0_helper1, _local1_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 9 {return;}
        let _param0 = _to_u64(data, 0);
        let _param1 = _to_i8(data, 8);
        test_function177(_param0 ,_param1);
    });
}
