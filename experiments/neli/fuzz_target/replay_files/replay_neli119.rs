#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function119(_param0 :u16 ,_param1 :u16) {
    let _local0 = <neli::consts::nl::NlmF as std::convert::From::<u16>>::from(_param0);
    let _local1 = <neli::consts::nl::NlmF as std::convert::From::<u16>>::from(_param1);
    let _ = <neli::consts::nl::NlmF as std::ops::BitOr::<neli::consts::nl::NlmF>>::bitor(_local0, _local1);
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
    if data.len() != 4 {return;}
    let _param0 = _to_u16(data, 0);
    let _param1 = _to_u16(data, 2);
    test_function119(_param0 ,_param1);

}