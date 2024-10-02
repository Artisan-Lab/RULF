extern crate subtle;
fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
}

fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

use subtle::ConstantTimeEq; // trait

fn test_function246(_param0 :i64 ,_param1 :i64 ,_param2 :i16) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i64 as subtle::ConstantTimeEq>::ct_ne(_local0_param0_helper1, _local0_param1_helper1);
    let _: subtle::CtOption::<i16> = subtle::CtOption::<i16>::new(_param2, _local0);
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
    if data.len() != 18 {return;}
    let _param0 = _to_i64(data, 0);
    let _param1 = _to_i64(data, 8);
    let _param2 = _to_i16(data, 16);
    test_function246(_param0 ,_param1 ,_param2);

}