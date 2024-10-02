extern crate serde_json;
fn _unwrap_option<T>(_opt: Option<T>) -> T {
    match _opt {
        Some(_t) => _t,
        None => {
            use std::process;
            process::exit(0);
        }
    }
}

fn _to_f64(data:&[u8], index: usize) -> f64 {
    let data_slice = &data[index..index+8];
    use std::convert::TryInto;
    let data_array:[u8;8] = data_slice.try_into().expect("slice with incorrect length");
    f64::from_le_bytes(data_array)
}

use serde::ser::Serializer; // trait

fn test_function219(_param0 :f64 ,_param1 :serde_json::value::Serializer) {
    let _local0 = serde_json::value::Number::from_f64(_param0);
    let _local1_param1_helper1 = _unwrap_option(_local0);
    let _local1_param1_helper2 = &(_local1_param1_helper1);
    let _: serde_json::Result::<serde_json::Value> = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_some(_param1, _local1_param1_helper2);
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
    if data.len() != 8 {return;}
    let _param0 = _to_f64(data, 0);
    let _param1 = serde_json::value::Serializer{};
    test_function219(_param0 ,_param1);

}