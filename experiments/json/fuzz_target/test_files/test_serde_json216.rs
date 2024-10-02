#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function216(_param0 :serde_json::value::Serializer) {
    let _ = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_unit(_param0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = serde_json::value::Serializer{};
        test_function216(_param0);
    });
}
