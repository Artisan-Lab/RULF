#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function32(_param0 :xorfilter::NoHash) {
    let _local0 = <std::vec::Vec::<u8> as std::convert::From::<xorfilter::NoHash>>::from(_param0);
    let _local1 = <xorfilter::BuildHasherDefault as std::convert::From::<std::vec::Vec::<u8, std::alloc::Global>>>::from(_local0);
    let _ = <std::vec::Vec::<u8> as std::convert::From::<xorfilter::BuildHasherDefault>>::from(_local1);
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
    let _param0 = xorfilter::NoHash{};
    test_function32(_param0);

}