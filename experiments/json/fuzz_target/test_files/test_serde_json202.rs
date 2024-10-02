#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn test_function202(_param0 :serde_json::value::Serializer ,_param1 :bool) {
    let _ = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_bool(_param0, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = serde_json::value::Serializer{};
        let _param1 = _to_bool(data, 0);
        test_function202(_param0 ,_param1);
    });
}
