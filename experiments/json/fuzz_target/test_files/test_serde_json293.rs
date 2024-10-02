#[macro_use]
extern crate afl;
extern crate serde_json;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
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

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_usize(data:&[u8], index:usize)->usize {
    _to_u64(data, index) as usize
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

use std::convert::From; // trait

fn test_function293(_param0 :i64 ,_param1 :usize) {
    let mut _local0 = <serde_json::Value as std::convert::From::<i64>>::from(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let _local1: std::option::Option::<&mut serde_json::Value> = serde_json::Value::get_mut(_local1_param0_helper1, _param1);
    let _: serde_json::Value = <serde_json::Value as std::convert::From::<std::option::Option::<&mut serde_json::Value>>>::from(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 16 {return;}
        let _param0 = _to_i64(data, 0);
        let _param1 = _to_usize(data, 8);
        test_function293(_param0 ,_param1);
    });
}
