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

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
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

fn test_function42(_param0 :i32 ,_param1 :u32 ,_param2 :u32 ,_param3 :u32 ,_param4 :&str) {
    let _local0 = chrono::naive::NaiveDate::from_ymd(_param0, _param1, _param2);
    let _local1_param0_helper1 = &(_local0);
    let _local1 = <chrono::naive::NaiveDate as chrono::Datelike>::with_ordinal(_local1_param0_helper1, _param3);
    let _local2_param0_helper1 = _unwrap_option(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _ = chrono::naive::NaiveDate::format(_local2_param0_helper2, _param4);
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
    if data.len() < 17 {return;}
    let dynamic_length = (data.len() - 16) / 1;
    let _param0 = _to_i32(data, 0);
    let _param1 = _to_u32(data, 4);
    let _param2 = _to_u32(data, 8);
    let _param3 = _to_u32(data, 12);
    let _param4 = _to_str(data, 16 + 0 * dynamic_length, data.len());
    test_function42(_param0 ,_param1 ,_param2 ,_param3 ,_param4);

}