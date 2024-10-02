#[macro_use]
extern crate afl;
extern crate serde_json;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

use std::convert::From; // trait

fn test_function235(_param0 :u8) {
    let _local0 = <serde_json::value::Number as std::convert::From::<u8>>::from(_param0);
    let _local1 = <serde_json::Value as std::convert::From::<serde_json::value::Number>>::from(_local0);
    let _: std::result::Result::<serde_json::Value, serde_json::Error> = serde_json::to_value(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function235(_param0);
    });
}
