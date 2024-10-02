#[macro_use]
extern crate afl;
extern crate serde_json;
fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
}

fn _to_isize(data:&[u8], index:usize)->isize {
    _to_i64(data, index) as isize
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

use std::convert::From; // trait

fn test_function283(_param0 :isize) {
    let _local0 = <serde_json::value::Number as std::convert::From::<isize>>::from(_param0);
    let _local1 = <serde_json::Value as std::convert::From::<serde_json::value::Number>>::from(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _: serde_json::Result::<std::vec::Vec::<u8>> = serde_json::ser::to_vec_pretty(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 8 {return;}
        let _param0 = _to_isize(data, 0);
        test_function283(_param0);
    });
}
