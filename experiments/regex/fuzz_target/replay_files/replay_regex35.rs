extern crate regex;
fn _unwrap_result<T, E>(_res: Result<T, E>) -> T {
    match _res {
        Ok(_t) => _t,
        Err(_) => {
            use std::process;
            process::exit(0);
        },
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

fn test_function35(_param0 :&str ,_param1 :&str ,_param2 :regex::NoExpand) {
    let _local0 = regex::Regex::new(_param0);
    let _local1_param0_helper1 = _unwrap_result(_local0);
    let _local1_param0_helper2 = &(_local1_param0_helper1);
    let mut _local1: std::borrow::Cow<'_, str> = regex::Regex::replace_all(_local1_param0_helper2, _param1, _param2);
    let _local2_param0_helper1 = &mut (_local1);
    let _ = <std::borrow::Cow<'_, str> as regex::Replacer>::no_expansion(_local2_param0_helper1);
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
    if data.len() < 3 {return;}
    let dynamic_length = (data.len() - 1) / 3;
    let _param0 = _to_str(data, 1 + 0 * dynamic_length, 1 + 1 * dynamic_length);
    let _param1 = _to_str(data, 1 + 1 * dynamic_length, 1 + 2 * dynamic_length);
    let _param2 = regex::NoExpand(_to_str(data, 1 + 2 * dynamic_length, data.len()));
    test_function35(_param0 ,_param1 ,_param2);

}