extern crate regex;
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

fn test_function50(_param0 :&str) {
    let mut _local0 = regex::escape(_param0);
    let mut _local1_param0_helper1 = &(_local0);
    let _local1_param0_helper2 = &mut (_local1_param0_helper1);
    let mut _local1 = <&std::string::String as regex::Replacer>::by_ref(_local1_param0_helper2);
    let _local2_param0_helper1 = &mut (_local1);
    let _: regex::ReplacerRef<'_, regex::ReplacerRef<'_, &std::string::String>> = <regex::ReplacerRef<'_, &std::string::String> as regex::Replacer>::by_ref(_local2_param0_helper1);
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
    test_function50(_param0);

}