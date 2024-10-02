#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_f64(data:&[u8], index: usize) -> f64 {
    let data_slice = &data[index..index+8];
    use std::convert::TryInto;
    let data_array:[u8;8] = data_slice.try_into().expect("slice with incorrect length");
    f64::from_le_bytes(data_array)
}

fn test_function214(_param0 :serde_json::value::Serializer ,_param1 :f64) {
    let _ = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_f64(_param0, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 8 {return;}
        let _param0 = serde_json::value::Serializer{};
        let _param1 = _to_f64(data, 0);
        test_function214(_param0 ,_param1);
    });
}
