#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_f64(data:&[u8], index: usize) -> f64 {
    let data_slice = &data[index..index+8];
    use std::convert::TryInto;
    let data_array:[u8;8] = data_slice.try_into().expect("slice with incorrect length");
    f64::from_le_bytes(data_array)
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function14(_param0 :f64 ,_param1 :&[u8]) {
    let _local0_param0_helper1 = &(_param0);
    let mut _local0 = <f64 as prost::Message>::encode_to_vec(_local0_param0_helper1);
    let _local1_param0_helper1 = &mut (_local0);
    let _: std::result::Result::<(), prost::DecodeError> = <std::vec::Vec::<u8> as prost::Message>::merge(_local1_param0_helper1, _param1);
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
    if data.len() < 9 {return;}
    let dynamic_length = (data.len() - 8) / 1;
    let _param0 = _to_f64(data, 0);
    let _param1 = _to_slice::<u8>(data, 8 + 0 * dynamic_length, data.len());
    test_function14(_param0 ,_param1);

}