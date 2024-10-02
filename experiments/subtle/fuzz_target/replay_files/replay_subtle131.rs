extern crate subtle;
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

fn _to_usize(data:&[u8], index:usize)->usize {
    _to_u64(data, index) as usize
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

use subtle::ConstantTimeEq; // trait

fn test_function131(_param0 :i8 ,_param1 :i8 ,_param2 :usize ,_param3 :i8 ,_param4 :i8 ,_param5 :usize) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1: subtle::CtOption::<usize> = subtle::CtOption::<usize>::new(_param2, _local0);
    let _local2_param0_helper1 = &(_param3);
    let _local2_param1_helper1 = &(_param4);
    let _local2 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local2_param0_helper1, _local2_param1_helper1);
    let _local3: subtle::CtOption::<usize> = subtle::CtOption::<usize>::new(_param5, _local2);
    let _local4_param0_helper1 = &(_local1);
    let _local4_param1_helper1 = &(_local3);
    let _: subtle::Choice = <subtle::CtOption::<usize> as subtle::ConstantTimeEq>::ct_ne(_local4_param0_helper1, _local4_param1_helper1);
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
    if data.len() != 20 {return;}
    let _param0 = _to_i8(data, 0);
    let _param1 = _to_i8(data, 1);
    let _param2 = _to_usize(data, 2);
    let _param3 = _to_i8(data, 10);
    let _param4 = _to_i8(data, 11);
    let _param5 = _to_usize(data, 12);
    test_function131(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5);

}