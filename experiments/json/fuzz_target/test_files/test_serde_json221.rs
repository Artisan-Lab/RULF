#[macro_use]
extern crate afl;
extern crate serde_json;
use serde::ser::Serializer; // trait

fn test_function221(_param0 :serde_json::value::Serializer) {
    let _local0 = serde_json::Map::<std::string::String, serde_json::Value>::new();
    let _local1_param1_helper1 = &(_local0);
    let _: serde_json::Result::<serde_json::Value> = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_some(_param0, _local1_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = serde_json::value::Serializer{};
        test_function221(_param0);
    });
}
