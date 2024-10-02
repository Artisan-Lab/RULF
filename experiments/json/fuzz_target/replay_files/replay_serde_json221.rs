extern crate serde_json;
use serde::ser::Serializer; // trait

fn test_function221(_param0 :serde_json::value::Serializer) {
    let _local0 = serde_json::Map::<std::string::String, serde_json::Value>::new();
    let _local1_param1_helper1 = &(_local0);
    let _: serde_json::Result::<serde_json::Value> = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_some(_param0, _local1_param1_helper1);
}

fn _read_data()-> Vec<u8> {
    use std::env;
    use std::process::exit;
    let args:Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("No crash filename provided");
        exit(-1);
    }
    use std::path::PathBuf;
    let crash_file_name = &args[1];
    let crash_path = PathBuf::from(crash_file_name);
    if !crash_path.is_file() {
        println!("Not a valid crash file");
        exit(-1);
    }
    use std::fs;
    let data =  fs::read(crash_path).unwrap();
    data
}

fn main() {
    let _content = _read_data();
    let data = &_content;
    println!("data = {:?}", data);
    println!("data len = {:?}", data.len());
    //actual body emit
    if data.len() != 0 {return;}
    let _param0 = serde_json::value::Serializer{};
    test_function221(_param0);

}