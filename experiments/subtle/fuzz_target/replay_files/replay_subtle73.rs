extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

use subtle::ConditionallySelectable; // trait
use subtle::ConstantTimeEq; // trait

fn test_function73(_param0 :&[u8] ,_param1 :&[u8] ,_param2 :u8 ,_param3 :u8) {
    let _local0: subtle::Choice = <[u8] as subtle::ConstantTimeEq>::ct_eq(_param0, _param1);
    let _local1_param0_helper1 = &(_param2);
    let _local1_param1_helper1 = &(_param3);
    let _ = <u8 as subtle::ConditionallySelectable>::conditional_select(_local1_param0_helper1, _local1_param1_helper1, _local0);
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
    if data.len() < 4 {return;}
    let dynamic_length = (data.len() - 2) / 2;
    let _param0 = _to_slice::<u8>(data, 2 + 0 * dynamic_length, 2 + 1 * dynamic_length);
    let _param1 = _to_slice::<u8>(data, 2 + 1 * dynamic_length, data.len());
    let _param2 = _to_u8(data, 0);
    let _param3 = _to_u8(data, 1);
    test_function73(_param0 ,_param1 ,_param2 ,_param3);

}