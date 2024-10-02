#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _unwrap_option<T>(_opt: Option<T>) -> T {
    match _opt {
        Some(_t) => _t,
        None => {
            use std::process;
            process::exit(0);
        }
    }
}

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_str(data:&[u8], start_index: usize, end_index: usize)->&str {
    let data_slice = &data[start_index..end_index];
    use std::str;
    match str::from_utf8(data_slice) {
        Ok(s)=>s,
        Err(_)=>{
            use std::process;
            process::exit(0);
        }
    }
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function0(_param0 :tui::layout::Rect ,_param1 :&str ,_param2 :u16 ,_param3 :u16 ,_param4 :u16) {
    let mut _local0 = tui::buffer::Buffer::empty(_param0);
    let _local1 = <std::string::String as std::convert::From::<&str>>::from(_param1);
    let _local2 = tui::style::Style::reset();
    let _local3 = tui::style::Modifier::from_bits(_param2);
    let _local4_param1_helper1 = _unwrap_option(_local3);
    let _local4 = tui::style::Style::add_modifier(_local2, _local4_param1_helper1);
    let _local5_param0_helper1 = &mut (_local0);
    let _ = tui::buffer::Buffer::set_string(_local5_param0_helper1, _param3, _param4, _local1, _local4);
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
    if data.len() < 15 {return;}
    let dynamic_length = (data.len() - 14) / 1;
    let _param0 = tui::layout::Rect{x: _to_u16(data, 0), y: _to_u16(data, 2), width: _to_u16(data, 4), height: _to_u16(data, 6)};
    let _param1 = _to_str(data, 14 + 0 * dynamic_length, data.len());
    let _param2 = _to_u16(data, 8);
    let _param3 = _to_u16(data, 10);
    let _param4 = _to_u16(data, 12);
    test_function0(_param0 ,_param1 ,_param2 ,_param3 ,_param4);

}