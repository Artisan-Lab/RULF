#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function203(_param0 :serde_json::value::Serializer ,_param1 :i8) {
    let _ = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_i8(_param0, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = serde_json::value::Serializer{};
        let _param1 = _to_i8(data, 0);
        test_function203(_param0 ,_param1);
    });
}
