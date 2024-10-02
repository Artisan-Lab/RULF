#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
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

fn test_function261(_param0 :u32 ,_param1 :u32 ,_param2 :u32 ,_param3 :i64 ,_param4 :u32 ,_param5 :i64 ,_param6 :u32) {
    let _local0 = chrono::naive::NaiveTime::from_hms(_param0, _param1, _param2);
    let _local1 = chrono::naive::NaiveDateTime::from_timestamp(_param3, _param4);
    let _local2 = chrono::naive::NaiveDateTime::from_timestamp(_param5, _param6);
    let _local3 = chrono::naive::NaiveDateTime::signed_duration_since(_local1, _local2);
    let _ = <chrono::naive::NaiveTime as std::ops::Add::<chrono::Duration>>::add(_local0, _local3);
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
    if data.len() != 36 {return;}
    let _param0 = _to_u32(data, 0);
    let _param1 = _to_u32(data, 4);
    let _param2 = _to_u32(data, 8);
    let _param3 = _to_i64(data, 12);
    let _param4 = _to_u32(data, 20);
    let _param5 = _to_i64(data, 24);
    let _param6 = _to_u32(data, 32);
    test_function261(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5 ,_param6);

}