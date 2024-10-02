#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u64(data:&[u8], index:usize)->u64 {
    let data0 = _to_u32(data, index) as u64;
    let data1 = _to_u32(data, index+4) as u64;
    data0 << 32 | data1
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_usize(data:&[u8], index:usize)->usize {
    _to_u64(data, index) as usize
}

fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect("slice with incorrect length");
    f32::from_le_bytes(data_array)
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function21(_param0 :fontdue::Metrics ,_param1 :fontdue::Metrics) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <fontdue::Metrics as std::cmp::PartialEq::<fontdue::Metrics>>::eq(_local0_param0_helper1, _local0_param1_helper1);
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
    if data.len() != 96 {return;}
    let _param0 = fontdue::Metrics{xmin: _to_i32(data, 0), ymin: _to_i32(data, 4), width: _to_usize(data, 8), height: _to_usize(data, 16), advance_width: _to_f32(data, 24), advance_height: _to_f32(data, 28), bounds: fontdue::OutlineBounds{xmin: _to_f32(data, 32), ymin: _to_f32(data, 36), width: _to_f32(data, 40), height: _to_f32(data, 44)}};
    let _param1 = fontdue::Metrics{xmin: _to_i32(data, 48), ymin: _to_i32(data, 52), width: _to_usize(data, 56), height: _to_usize(data, 64), advance_width: _to_f32(data, 72), advance_height: _to_f32(data, 76), bounds: fontdue::OutlineBounds{xmin: _to_f32(data, 80), ymin: _to_f32(data, 84), width: _to_f32(data, 88), height: _to_f32(data, 92)}};
    test_function21(_param0 ,_param1);

}