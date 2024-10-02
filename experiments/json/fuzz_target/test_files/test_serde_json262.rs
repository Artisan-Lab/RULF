#[macro_use]
extern crate afl;
extern crate serde_json;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

use std::convert::From; // trait

fn test_function262(_param0 :i8) {
    let _local0 = <serde_json::value::Number as std::convert::From::<i8>>::from(_param0);
    let _local1 = <serde_json::Value as std::convert::From::<serde_json::value::Number>>::from(_local0);
    let _: std::result::Result::<serde_json::Value, serde_json::Error> = serde_json::value::to_value(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_i8(data, 0);
        test_function262(_param0);
    });
}
