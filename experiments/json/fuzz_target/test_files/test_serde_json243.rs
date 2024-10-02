#[macro_use]
extern crate afl;
extern crate serde_json;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

use serde::de::Error; // trait
use std::convert::From; // trait

fn test_function243(_param0 :u16) {
    let _local0 = <serde_json::value::Number as std::convert::From::<u16>>::from(_param0);
    let _local1: serde_json::Error = <serde_json::Error as serde::de::Error>::custom(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _ = serde_json::Error::column(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u16(data, 0);
        test_function243(_param0);
    });
}
