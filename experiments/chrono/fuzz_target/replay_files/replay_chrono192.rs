#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function192(_param0 :chrono::offset::Utc ,_param1 :chrono::offset::Utc) {
    let _local0_param0_helper1 = &(_param0);
    let _local0 = <chrono::offset::Utc as chrono::offset::Offset>::fix(_local0_param0_helper1);
    let _local1_param0_helper1 = &(_param1);
    let _local1 = <chrono::offset::Utc as chrono::offset::Offset>::fix(_local1_param0_helper1);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _ = <chrono::offset::FixedOffset as std::cmp::PartialEq::<chrono::offset::FixedOffset>>::eq(_local2_param0_helper1, _local2_param1_helper1);
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
    let _param0 = chrono::offset::Utc{};
    let _param1 = chrono::offset::Utc{};
    test_function192(_param0 ,_param1);

}