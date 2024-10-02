#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function23(_param0 :&[u64]) {
    let _local0 = <xorfilter::BuildHasherDefault as std::default::Default>::default();
    let mut _local1: xorfilter::Xor8::<xorfilter::BuildHasherDefault> = xorfilter::Xor8::<xorfilter::BuildHasherDefault>::with_hasher(_local0);
    let _local2_param0_helper1 = &mut (_local1);
    let _ = xorfilter::Xor8::<xorfilter::BuildHasherDefault>::populate_keys(_local2_param0_helper1, _param0);
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
    if data.len() < 8 {return;}
    let dynamic_length = (data.len() - 0) / 1;
    let _param0 = _to_slice::<u64>(data, 0 + 0 * dynamic_length, data.len());
    test_function23(_param0);

}