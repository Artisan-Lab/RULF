#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
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

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn test_function147(_param0 :u32 ,_param1 :&str ,_param2 :u32 ,_param3 :u32 ,_param4 :bool) {
    let _local0 = flate2::GzBuilder::new();
    let _local1 = flate2::GzBuilder::mtime(_local0, _param0);
    let _local2 = <std::vec::Vec::<u8, std::alloc::Global> as std::convert::From::<&str>>::from(_param1);
    let _local3 = flate2::Compression::new(_param2);
    let _local4: flate2::write::GzEncoder::<std::vec::Vec::<u8, std::alloc::Global>> = flate2::GzBuilder::write(_local1, _local2, _local3);
    let _local5 = flate2::Compression::new(_param3);
    let _local6 = flate2::Compress::new(_local5, _param4);
    let _local7: flate2::write::ZlibEncoder::<flate2::write::GzEncoder::<std::vec::Vec::<u8, std::alloc::Global>>> = flate2::write::ZlibEncoder::<flate2::write::GzEncoder::<std::vec::Vec::<u8, std::alloc::Global>>>::new_with_compress(_local4, _local6);
    let _: std::io::Result::<flate2::write::GzEncoder::<std::vec::Vec::<u8, std::alloc::Global>>> = flate2::write::ZlibEncoder::<flate2::write::GzEncoder::<std::vec::Vec::<u8, std::alloc::Global>>>::flush_finish(_local7);
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
    if data.len() < 14 {return;}
    let dynamic_length = (data.len() - 13) / 1;
    let _param0 = _to_u32(data, 0);
    let _param1 = _to_str(data, 13 + 0 * dynamic_length, data.len());
    let _param2 = _to_u32(data, 4);
    let _param3 = _to_u32(data, 8);
    let _param4 = _to_bool(data, 12);
    test_function147(_param0 ,_param1 ,_param2 ,_param3 ,_param4);

}