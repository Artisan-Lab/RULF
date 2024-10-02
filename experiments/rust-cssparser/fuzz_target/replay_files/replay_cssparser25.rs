#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
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

fn test_function25(_param0 :&str ,_param1 :&str) {
    let mut _local0 = cssparser::ParserInput::<'_>::new(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let mut _local1 = cssparser::Parser::<'_, '_>::new(_local1_param0_helper1);
    let mut _local2 = cssparser::ParserInput::<'_>::new(_param1);
    let _local3_param0_helper1 = &mut (_local2);
    let _local3 = cssparser::Parser::<'_, '_>::new(_local3_param0_helper1);
    let _local4_param0_helper1 = &(_local3);
    let _local4 = cssparser::Parser::<'_, '_>::state(_local4_param0_helper1);
    let _local5_param0_helper1 = &mut (_local1);
    let _local5_param1_helper1 = &(_local4);
    let _ = cssparser::Parser::<'_, '_>::reset(_local5_param0_helper1, _local5_param1_helper1);
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
    if data.len() < 2 {return;}
    let dynamic_length = (data.len() - 0) / 2;
    let _param0 = _to_str(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
    let _param1 = _to_str(data, 0 + 1 * dynamic_length, data.len());
    test_function25(_param0 ,_param1);

}