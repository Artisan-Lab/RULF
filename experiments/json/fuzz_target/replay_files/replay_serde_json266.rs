extern crate serde_json;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

use serde::ser::Error; // trait
use std::convert::From; // trait

fn test_function266(_param0 :i8) {
    let _local0 = <serde_json::value::Number as std::convert::From::<i8>>::from(_param0);
    let _local1: serde_json::Error = <serde_json::Error as serde::ser::Error>::custom(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _ = serde_json::Error::is_eof(_local2_param0_helper1);
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
    if data.len() != 1 {return;}
    let _param0 = _to_i8(data, 0);
    test_function266(_param0);

}