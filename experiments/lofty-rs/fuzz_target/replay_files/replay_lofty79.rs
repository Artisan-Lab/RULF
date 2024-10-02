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

fn test_function79(_param0 :&[u8] ,_param1 :&[u8] ,_param2 :&str) {
    let _local0 = lofty::FileType::from_buffer(_param0);
    let _local1_param0_helper1 = _unwrap_option(_local0);
    let _local1_param0_helper2 = &(_local1_param0_helper1);
    let _local1 = lofty::FileType::primary_tag_type(_local1_param0_helper2);
    let _local2 = lofty::Tag::new(_local1);
    let _local3 = lofty::FileType::from_buffer(_param1);
    let _local4_param0_helper1 = _unwrap_option(_local3);
    let _local4_param0_helper2 = &(_local4_param0_helper1);
    let _local4 = lofty::FileType::primary_tag_type(_local4_param0_helper2);
    let _local5 = lofty::ItemKey::from_key(_local4, _param2);
    let _local6_param0_helper1 = &(_local2);
    let _local6_param1_helper1 = &(_local5);
    let _ = lofty::Tag::get(_local6_param0_helper1, _local6_param1_helper1);
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
    if data.len() < 3 {return;}
    let dynamic_length = (data.len() - 0) / 3;
    let _param0 = _to_slice::<u8>(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
    let _param1 = _to_slice::<u8>(data, 0 + 1 * dynamic_length, 0 + 2 * dynamic_length);
    let _param2 = _to_str(data, 0 + 2 * dynamic_length, data.len());
    test_function79(_param0 ,_param1 ,_param2);

}