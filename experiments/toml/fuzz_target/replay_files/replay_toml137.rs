#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function137(_param0 :toml_datetime::DatetimeParseError) {
    let _local0: toml::ser::Error = <toml::ser::Error as serde::ser::Error>::custom(_param0);
    let _local1: toml::de::Error = <toml::de::Error as serde::de::Error>::custom(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _ = toml::de::Error::message(_local2_param0_helper1);
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
    let _param0 = toml_datetime::DatetimeParseError{};
    test_function137(_param0);

}