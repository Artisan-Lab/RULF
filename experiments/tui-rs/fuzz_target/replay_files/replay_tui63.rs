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

fn test_function63(_param0 :u16 ,_param1 :tui::layout::Rect) {
    let _local0 = <tui::layout::Layout as std::default::Default>::default();
    let _local1 = tui::layout::Layout::vertical_margin(_local0, _param0);
    let _local2_param0_helper1 = &(_local1);
    let _ = tui::layout::Layout::split(_local2_param0_helper1, _param1);
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
    if data.len() != 10 {return;}
    let _param0 = _to_u16(data, 0);
    let _param1 = tui::layout::Rect{x: _to_u16(data, 2), y: _to_u16(data, 4), width: _to_u16(data, 6), height: _to_u16(data, 8)};
    test_function63(_param0 ,_param1);

}