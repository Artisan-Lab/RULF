#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function73(_param0 :cookie::prefix::Host ,_param1 :cookie::prefix::Host) {
    let mut _local0 = cookie::CookieJar::new();
    let _local1_param0_helper1 = &mut (_local0);
    let mut _local1: cookie::prefix::PrefixedJar::<cookie::prefix::Host, &mut cookie::CookieJar> = cookie::CookieJar::prefixed_mut(_local1_param0_helper1, _param0);
    let _local2_param0_helper1 = &mut (_local1);
    let _local2_param1_helper1 = &(_param1);
    let _ = cookie::prefix::PrefixedJar::<cookie::prefix::Host, &mut cookie::CookieJar>::add_original(_local2_param0_helper1, _local2_param1_helper1);
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
    let _param0 = cookie::prefix::Host{};
    let _param1 = cookie::prefix::Host{};
    test_function73(_param0 ,_param1);

}