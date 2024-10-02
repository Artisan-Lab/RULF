#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function36(_param0 :xorfilter::NoHash ,_param1 :xorfilter::NoHash) {
    let _local0 = <std::vec::Vec::<u8> as std::convert::From::<xorfilter::NoHash>>::from(_param0);
    let _local1 = <xorfilter::BuildHasherDefault as std::convert::From::<std::vec::Vec::<u8, std::alloc::Global>>>::from(_local0);
    let _local2: xorfilter::Xor8::<xorfilter::BuildHasherDefault> = xorfilter::Xor8::<xorfilter::BuildHasherDefault>::with_hasher(_local1);
    let _local3 = <std::vec::Vec::<u8> as std::convert::From::<xorfilter::NoHash>>::from(_param1);
    let _local4 = <xorfilter::BuildHasherDefault as std::convert::From::<std::vec::Vec::<u8, std::alloc::Global>>>::from(_local3);
    let _local5: xorfilter::Xor8::<xorfilter::BuildHasherDefault> = xorfilter::Xor8::<xorfilter::BuildHasherDefault>::with_hasher(_local4);
    let _local6_param0_helper1 = &(_local2);
    let _local6_param1_helper1 = &(_local5);
    let _: bool = <xorfilter::Xor8::<xorfilter::BuildHasherDefault> as std::cmp::PartialEq::<xorfilter::Xor8::<xorfilter::BuildHasherDefault>>>::eq(_local6_param0_helper1, _local6_param1_helper1);
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
    let _param1 = xorfilter::NoHash{};
    test_function36(_param0 ,_param1);

}