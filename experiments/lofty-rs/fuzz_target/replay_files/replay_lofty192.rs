#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn test_function192(_param0 :lofty::id3::v2::AudioTextFrameFlags ,_param1 :lofty::id3::v2::AudioTextFrameFlags) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <lofty::id3::v2::AudioTextFrameFlags as std::cmp::PartialOrd::<lofty::id3::v2::AudioTextFrameFlags>>::partial_cmp(_local0_param0_helper1, _local0_param1_helper1);
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
    let _param0 = lofty::id3::v2::AudioTextFrameFlags{scrambling: _to_bool(data, 0)};
    let _param1 = lofty::id3::v2::AudioTextFrameFlags{scrambling: _to_bool(data, 1)};
    test_function192(_param0 ,_param1);

}