extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

use subtle::ConditionallySelectable; // trait
use subtle::ConstantTimeEq; // trait

fn test_function96(_param0 :i8 ,_param1 :i8 ,_param2 :u8 ,_param3 :i8 ,_param4 :i8 ,_param5 :u8 ,_param6 :i8 ,_param7 :i8) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let mut _local1: subtle::CtOption::<u8> = subtle::CtOption::<u8>::new(_param2, _local0);
    let _local2_param0_helper1 = &(_param3);
    let _local2_param1_helper1 = &(_param4);
    let _local2 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local2_param0_helper1, _local2_param1_helper1);
    let _local3: subtle::CtOption::<u8> = subtle::CtOption::<u8>::new(_param5, _local2);
    let _local4_param0_helper1 = &(_param6);
    let _local4_param1_helper1 = &(_param7);
    let _local4 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local4_param0_helper1, _local4_param1_helper1);
    let _local5_param0_helper1 = &mut (_local1);
    let _local5_param1_helper1 = &(_local3);
    let _ = <subtle::CtOption::<u8> as subtle::ConditionallySelectable>::conditional_assign(_local5_param0_helper1, _local5_param1_helper1, _local4);
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
    if data.len() != 8 {return;}
    let _param0 = _to_i8(data, 0);
    let _param1 = _to_i8(data, 1);
    let _param2 = _to_u8(data, 2);
    let _param3 = _to_i8(data, 3);
    let _param4 = _to_i8(data, 4);
    let _param5 = _to_u8(data, 5);
    let _param6 = _to_i8(data, 6);
    let _param7 = _to_i8(data, 7);
    test_function96(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5 ,_param6 ,_param7);

}