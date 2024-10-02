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

fn test_function53(_param0 :i32 ,_param1 :&str ,_param2 :&str) {
    let _local0 = chrono::offset::FixedOffset::east_opt(_param0);
    let _local1_param0_helper1 = _unwrap_option(_local0);
    let _local1_param0_helper2 = &(_local1_param0_helper1);
    let _ = <chrono::offset::FixedOffset as chrono::offset::TimeZone>::datetime_from_str(_local1_param0_helper2, _param1, _param2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 6 {return;}
        let dynamic_length = (data.len() - 4) / 2;
        let _param0 = _to_i32(data, 0);
        let _param1 = _to_str(data, 4 + 0 * dynamic_length, 4 + 1 * dynamic_length);
        let _param2 = _to_str(data, 4 + 1 * dynamic_length, data.len());
        test_function53(_param0 ,_param1 ,_param2);
    });
}
