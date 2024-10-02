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

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function181(_param0 :u32 ,_param1 :u32 ,_param2 :u32 ,_param3 :u32) {
    let _local0 = chrono::naive::NaiveTime::from_hms(_param0, _param1, _param2);
    let _local1_param0_helper1 = &(_local0);
    let _local1 = <chrono::naive::NaiveTime as chrono::Timelike>::with_second(_local1_param0_helper1, _param3);
    let _local2_param0_helper1 = _unwrap_option(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _ = <chrono::naive::NaiveTime as chrono::Timelike>::num_seconds_from_midnight(_local2_param0_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 16 {return;}
        let _param0 = _to_u32(data, 0);
        let _param1 = _to_u32(data, 4);
        let _param2 = _to_u32(data, 8);
        let _param3 = _to_u32(data, 12);
        test_function181(_param0 ,_param1 ,_param2 ,_param3);
    });
}
