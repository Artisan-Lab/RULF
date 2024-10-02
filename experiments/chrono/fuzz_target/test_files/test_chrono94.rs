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

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function94(_param0 :chrono::offset::Local ,_param1 :i64) {
    let _local0_param0_helper1 = &(_param0);
    let _local0 = <chrono::offset::Local as chrono::offset::TimeZone>::timestamp_nanos(_local0_param0_helper1, _param1);
    let _local1 = <chrono::DateTime::<chrono::offset::FixedOffset> as std::convert::From::<chrono::DateTime::<chrono::offset::Local>>>::from(_local0);
    let _ = <chrono::DateTime::<chrono::offset::Local> as std::convert::From::<chrono::DateTime::<chrono::offset::FixedOffset>>>::from(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 8 {return;}
        let _param0 = chrono::offset::Local{};
        let _param1 = _to_i64(data, 0);
        test_function94(_param0 ,_param1);
    });
}
