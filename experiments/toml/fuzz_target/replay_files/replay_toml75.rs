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

fn test_function75(_param0 :f64) {
    let _local0 = <toml::Value as std::convert::From::<f64>>::from(_param0);
    let _local1 = <toml::Value as serde::de::IntoDeserializer::<'_, toml::de::Error>>::into_deserializer(_local0);
    let _: toml::ser::Error = <toml::ser::Error as serde::ser::Error>::custom(_local1);
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
    test_function75(_param0);

}