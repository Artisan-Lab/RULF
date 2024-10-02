#[macro_use]
extern crate afl;
extern crate serde_json;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

use std::convert::From; // trait

fn test_function267(_param0 :i16) {
    let _local0 = <serde_json::value::Number as std::convert::From::<i16>>::from(_param0);
    let _local1 = <serde_json::Value as std::convert::From::<serde_json::value::Number>>::from(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _: serde_json::Result::<std::string::String> = serde_json::ser::to_string_pretty(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_i16(data, 0);
        test_function267(_param0);
    });
}
