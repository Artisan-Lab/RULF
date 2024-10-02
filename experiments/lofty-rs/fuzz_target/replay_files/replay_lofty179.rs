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

fn test_function179(_param0 :lofty::musepack::sv8::ReplayGain ,_param1 :lofty::musepack::sv8::ReplayGain) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <lofty::musepack::sv8::ReplayGain as std::cmp::PartialEq::<lofty::musepack::sv8::ReplayGain>>::eq(_local0_param0_helper1, _local0_param1_helper1);
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
    if data.len() != 18 {return;}
    let _param0 = lofty::musepack::sv8::ReplayGain{version: _to_u8(data, 0), title_gain: _to_u16(data, 1), title_peak: _to_u16(data, 3), album_gain: _to_u16(data, 5), album_peak: _to_u16(data, 7)};
    let _param1 = lofty::musepack::sv8::ReplayGain{version: _to_u8(data, 9), title_gain: _to_u16(data, 10), title_peak: _to_u16(data, 12), album_gain: _to_u16(data, 14), album_peak: _to_u16(data, 16)};
    test_function179(_param0 ,_param1);

}