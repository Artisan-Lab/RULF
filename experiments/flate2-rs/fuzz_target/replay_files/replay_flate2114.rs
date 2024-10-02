#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
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

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function114(_param0 :&str ,_param1 :&[u8]) {
    let _local0 = <std::vec::Vec::<u8, std::alloc::Global> as std::convert::From::<&str>>::from(_param0);
    let mut _local1: flate2::CrcWriter::<std::vec::Vec::<u8, std::alloc::Global>> = flate2::CrcWriter::<std::vec::Vec::<u8, std::alloc::Global>>::new(_local0);
    let _local2_param0_helper1 = &mut (_local1);
    let _: std::io::Result::<usize> = <flate2::CrcWriter::<std::vec::Vec::<u8, std::alloc::Global>> as std::io::Write>::write(_local2_param0_helper1, _param1);
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
    if data.len() < 2 {return;}
    let dynamic_length = (data.len() - 0) / 2;
    let _param0 = _to_str(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
    let _param1 = _to_slice::<u8>(data, 0 + 1 * dynamic_length, data.len());
    test_function114(_param0 ,_param1);

}