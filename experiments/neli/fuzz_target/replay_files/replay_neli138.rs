#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function138(_param0 :u8 ,_param1 :u8) {
    let _local0 = <neli::consts::genl::CtrlCmd as std::convert::From::<u8>>::from(_param0);
    let _local1 = <neli::consts::genl::CtrlCmd as std::convert::From::<u8>>::from(_param1);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _ = <neli::consts::genl::CtrlCmd as std::cmp::PartialOrd::<neli::consts::genl::CtrlCmd>>::partial_cmp(_local2_param0_helper1, _local2_param1_helper1);
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
    if data.len() != 2 {return;}
    let _param0 = _to_u8(data, 0);
    let _param1 = _to_u8(data, 1);
    test_function138(_param0 ,_param1);

}