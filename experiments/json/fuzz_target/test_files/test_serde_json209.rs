#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function209(_param0 :serde_json::value::Serializer ,_param1 :u16) {
    let _ = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_u16(_param0, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = serde_json::value::Serializer{};
        let _param1 = _to_u16(data, 0);
        test_function209(_param0 ,_param1);
    });
}
