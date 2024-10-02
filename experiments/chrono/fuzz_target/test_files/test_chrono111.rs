#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
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

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
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

fn test_function111(_param0 :i64 ,_param1 :u32 ,_param2 :chrono::offset::Local) {
    let _local0 = chrono::naive::NaiveDateTime::from_timestamp(_param0, _param1);
    let _local1_param0_helper1 = &(_param2);
    let _local1_param1_helper1 = &(_local0);
    let _local1 = <chrono::offset::Local as chrono::offset::TimeZone>::offset_from_utc_datetime(_local1_param0_helper1, _local1_param1_helper1);
    let _local2_param0_helper1 = &(_local1);
    let _ = <chrono::offset::Local as chrono::offset::TimeZone>::from_offset(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 12 {return;}
        let _param0 = _to_i64(data, 0);
        let _param1 = _to_u32(data, 8);
        let _param2 = chrono::offset::Local{};
        test_function111(_param0 ,_param1 ,_param2);
    });
}
