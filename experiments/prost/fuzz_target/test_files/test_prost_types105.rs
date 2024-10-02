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

fn test_function105(mut _param0 :prost_types::Timestamp) {
    let _local0_param0_helper1 = &mut (_param0);
    let _ = prost_types::Timestamp::normalize(_local0_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 12 {return;}
        let _param0 = prost_types::Timestamp{seconds: _to_i64(data, 0), nanos: _to_i32(data, 8)};
        test_function105(_param0);
    });
}
