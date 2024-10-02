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

fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
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

fn test_function299(_param0 :i32 ,_param1 :u32 ,_param2 :u32 ,_param3 :i64) {
    let _local0 = chrono::naive::NaiveDate::from_ymd(_param0, _param1, _param2);
    let _local1 = <chrono::Weekday as num_traits::cast::FromPrimitive>::from_i64(_param3);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = _unwrap_option(_local1);
    let _local2 = chrono::naive::NaiveDate::week(_local2_param0_helper1, _local2_param1_helper1);
    let _local3_param0_helper1 = &(_local2);
    let _ = chrono::naive::NaiveWeek::last_day(_local3_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 20 {return;}
        let _param0 = _to_i32(data, 0);
        let _param1 = _to_u32(data, 4);
        let _param2 = _to_u32(data, 8);
        let _param3 = _to_i64(data, 12);
        test_function299(_param0 ,_param1 ,_param2 ,_param3);
    });
}
