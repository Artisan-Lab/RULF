#[macro_use]
extern crate afl;
extern crate serde_json;
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

use serde::de::Error; // trait
use std::convert::From; // trait

fn test_function275(_param0 :i32) {
    let _local0 = <serde_json::value::Number as std::convert::From::<i32>>::from(_param0);
    let _local1: serde_json::Error = <serde_json::Error as serde::de::Error>::custom(_local0);
    let _ = <std::io::Error as std::convert::From::<serde_json::Error>>::from(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_i32(data, 0);
        test_function275(_param0);
    });
}
