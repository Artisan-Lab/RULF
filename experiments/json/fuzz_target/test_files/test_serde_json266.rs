#[macro_use]
extern crate afl;
extern crate serde_json;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

use serde::ser::Error; // trait
use std::convert::From; // trait

fn test_function266(_param0 :i8) {
    let _local0 = <serde_json::value::Number as std::convert::From::<i8>>::from(_param0);
    let _local1: serde_json::Error = <serde_json::Error as serde::ser::Error>::custom(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _ = serde_json::Error::is_eof(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_i8(data, 0);
        test_function266(_param0);
    });
}
