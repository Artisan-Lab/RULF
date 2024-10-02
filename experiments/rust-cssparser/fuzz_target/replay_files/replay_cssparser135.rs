#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function135(_param0 :i16 ,_param1 :u8) {
    let _local0_param0_helper1 = &(_param0);
    let mut _local0 = <i16 as cssparser::ToCss>::to_css_string(_local0_param0_helper1);
    let _local1_param0_helper1 = &(_param1);
    let _local1_param1_helper1 = &mut (_local0);
    let _: std::fmt::Result = <u8 as cssparser::ToCss>::to_css(_local1_param0_helper1, _local1_param1_helper1);
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
    if data.len() != 3 {return;}
    let _param0 = _to_i16(data, 0);
    let _param1 = _to_u8(data, 2);
    test_function135(_param0 ,_param1);

}