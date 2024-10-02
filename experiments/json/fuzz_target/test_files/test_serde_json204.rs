#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function204(_param0 :serde_json::value::Serializer ,_param1 :i16) {
    let _ = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_i16(_param0, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = serde_json::value::Serializer{};
        let _param1 = _to_i16(data, 0);
        test_function204(_param0 ,_param1);
    });
}
