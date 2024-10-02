#[macro_use]
extern crate afl;
extern crate serde_json;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

use serde::ser::Error; // trait
use std::convert::From; // trait

fn test_function239(_param0 :u8) {
    let _local0 = <serde_json::value::Number as std::convert::From::<u8>>::from(_param0);
    let _local1: serde_json::Error = <serde_json::Error as serde::ser::Error>::custom(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _ = serde_json::Error::column(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function239(_param0);
    });
}
