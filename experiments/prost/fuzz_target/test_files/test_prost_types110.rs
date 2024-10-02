#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
}

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

fn test_function110(_param0 :prost_types::Timestamp ,_param1 :prost_types::Timestamp) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <prost_types::Timestamp as std::cmp::PartialEq::<prost_types::Timestamp>>::eq(_local0_param0_helper1, _local0_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 24 {return;}
        let _param0 = prost_types::Timestamp{seconds: _to_i64(data, 0), nanos: _to_i32(data, 8)};
        let _param1 = prost_types::Timestamp{seconds: _to_i64(data, 12), nanos: _to_i32(data, 20)};
        test_function110(_param0 ,_param1);
    });
}
