extern crate regex;
fn _unwrap_option<T>(_opt: Option<T>) -> T {
    match _opt {
        Some(_t) => _t,
        None => {
            use std::process;
            process::exit(0);
        }
    }
}

fn _to_str(data:&[u8], start_index: usize, end_index: usize)->&str {
    let data_slice = &data[start_index..end_index];
    use std::str;
    match str::from_utf8(data_slice) {
        Ok(s)=>s,
        Err(_)=>{
            use std::process;
            process::exit(0);
        }
    }
}

use regex::Replacer;

fn test_function39(mut _param0 :&str) {
    let _local0_param0_helper1 = &mut (_param0);
    let mut _local0 = <&str as regex::Replacer>::no_expansion(_local0_param0_helper1);
    let mut _local1_param0_helper1 = _unwrap_option(_local0);
    let _local1_param0_helper2 = &mut (_local1_param0_helper1);
    let mut _local1 = <std::borrow::Cow<'_, str> as regex::Replacer>::by_ref(_local1_param0_helper2);
    let _local2_param0_helper1 = &mut (_local1);
    let _: core::option::Option<std::borrow::Cow<'_, str>> = <regex::ReplacerRef<'_, std::borrow::Cow<'_, str>> as regex::Replacer>::no_expansion(_local2_param0_helper1);
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
    if data.len() < 1 {return;}
    let dynamic_length = (data.len() - 0) / 1;
    let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
    test_function39(_param0);

}