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

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function108(_param0 :i64 ,_param1 :u8 ,_param2 :u8 ,_param3 :u8 ,_param4 :u8 ,_param5 :u8) {
    let _ = prost_types::Timestamp::date_time(_param0, _param1, _param2, _param3, _param4, _param5);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 13 {return;}
        let _param0 = _to_i64(data, 0);
        let _param1 = _to_u8(data, 8);
        let _param2 = _to_u8(data, 9);
        let _param3 = _to_u8(data, 10);
        let _param4 = _to_u8(data, 11);
        let _param5 = _to_u8(data, 12);
        test_function108(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5);
    });
}
