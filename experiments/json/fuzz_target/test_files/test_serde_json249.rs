#[macro_use]
extern crate afl;
extern crate serde_json;
fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

use serde::ser::Error; // trait
use std::convert::From; // trait

fn test_function249(_param0 :u32) {
    let _local0 = <serde_json::value::Number as std::convert::From::<u32>>::from(_param0);
    let _local1: serde_json::Error = <serde_json::Error as serde::ser::Error>::custom(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _ = serde_json::Error::is_io(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_u32(data, 0);
        test_function249(_param0);
    });
}
