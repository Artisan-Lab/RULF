extern crate subtle;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

use subtle::ConditionallySelectable; // trait
use subtle::ConstantTimeEq; // trait

fn test_function61(_param0 :&[u8] ,_param1 :&[u8] ,mut _param2 :i16 ,_param3 :i16) {
    let _local0: subtle::Choice = <[u8] as subtle::ConstantTimeEq>::ct_eq(_param0, _param1);
    let _local1_param0_helper1 = &mut (_param2);
    let _local1_param1_helper1 = &(_param3);
    let _ = <i16 as subtle::ConditionallySelectable>::conditional_assign(_local1_param0_helper1, _local1_param1_helper1, _local0);
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
    if data.len() < 6 {return;}
    let dynamic_length = (data.len() - 4) / 2;
    let _param0 = _to_slice::<u8>(data, 4 + 0 * dynamic_length, 4 + 1 * dynamic_length);
    let _param1 = _to_slice::<u8>(data, 4 + 1 * dynamic_length, data.len());
    let _param2 = _to_i16(data, 0);
    let _param3 = _to_i16(data, 2);
    test_function61(_param0 ,_param1 ,_param2 ,_param3);

}