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

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn test_function188(_param0 :lofty::musepack::sv8::StreamHeader ,_param1 :lofty::musepack::sv8::StreamHeader) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <lofty::musepack::sv8::StreamHeader as std::cmp::PartialEq::<lofty::musepack::sv8::StreamHeader>>::eq(_local0_param0_helper1, _local0_param1_helper1);
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
    if data.len() != 60 {return;}
    let _param0 = lofty::musepack::sv8::StreamHeader{crc: _to_u32(data, 0), stream_version: _to_u8(data, 4), sample_count: _to_u64(data, 5), beginning_silence: _to_u64(data, 13), sample_rate: _to_u32(data, 21), max_used_bands: _to_u8(data, 25), channels: _to_u8(data, 26), ms_used: _to_bool(data, 27), audio_block_frames: _to_u16(data, 28)};
    let _param1 = lofty::musepack::sv8::StreamHeader{crc: _to_u32(data, 30), stream_version: _to_u8(data, 34), sample_count: _to_u64(data, 35), beginning_silence: _to_u64(data, 43), sample_rate: _to_u32(data, 51), max_used_bands: _to_u8(data, 55), channels: _to_u8(data, 56), ms_used: _to_bool(data, 57), audio_block_frames: _to_u16(data, 58)};
    test_function188(_param0 ,_param1);

}