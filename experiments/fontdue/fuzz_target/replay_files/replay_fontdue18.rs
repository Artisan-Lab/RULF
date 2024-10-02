#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect("slice with incorrect length");
    f32::from_le_bytes(data_array)
}

fn test_function18(_param0 :fontdue::LineMetrics ,_param1 :fontdue::LineMetrics) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <fontdue::LineMetrics as std::cmp::PartialEq::<fontdue::LineMetrics>>::eq(_local0_param0_helper1, _local0_param1_helper1);
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
    if data.len() != 32 {return;}
    let _param0 = fontdue::LineMetrics{ascent: _to_f32(data, 0), descent: _to_f32(data, 4), line_gap: _to_f32(data, 8), new_line_size: _to_f32(data, 12)};
    let _param1 = fontdue::LineMetrics{ascent: _to_f32(data, 16), descent: _to_f32(data, 20), line_gap: _to_f32(data, 24), new_line_size: _to_f32(data, 28)};
    test_function18(_param0 ,_param1);

}