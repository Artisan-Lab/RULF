extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
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

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

use subtle::ConstantTimeEq; // trait
use std::ops::BitOrAssign; // trait

fn test_function46(_param0 :&[u8] ,_param1 :&[u8] ,_param2 :usize ,_param3 :usize) {
    let mut _local0: subtle::Choice = <[u8] as subtle::ConstantTimeEq>::ct_ne(_param0, _param1);
    let _local1_param0_helper1 = &(_param2);
    let _local1_param1_helper1 = &(_param3);
    let _local1 = <usize as subtle::ConstantTimeEq>::ct_ne(_local1_param0_helper1, _local1_param1_helper1);
    let _local2_param0_helper1 = &mut (_local0);
    let _ = <subtle::Choice as std::ops::BitOrAssign::<subtle::Choice>>::bitor_assign(_local2_param0_helper1, _local1);
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
    if data.len() < 18 {return;}
    let dynamic_length = (data.len() - 16) / 2;
    let _param0 = _to_slice::<u8>(data, 16 + 0 * dynamic_length, 16 + 1 * dynamic_length);
    let _param1 = _to_slice::<u8>(data, 16 + 1 * dynamic_length, data.len());
    let _param2 = _to_usize(data, 0);
    let _param3 = _to_usize(data, 8);
    test_function46(_param0 ,_param1 ,_param2 ,_param3);

}