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

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn test_function221(_param0 :u64 ,_param1 :u64) {
    let _local0 = <chrono::Month as num_traits::cast::FromPrimitive>::from_u64(_param0);
    let _local1 = <chrono::Month as num_traits::cast::FromPrimitive>::from_u64(_param1);
    let _local2_param0_helper1 = _unwrap_option(_local0);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2_param1_helper1 = _unwrap_option(_local1);
    let _local2_param1_helper2 = &(_local2_param1_helper1);
    let _ = <chrono::Month as std::cmp::Ord>::cmp(_local2_param0_helper2, _local2_param1_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 16 {return;}
        let _param0 = _to_u64(data, 0);
        let _param1 = _to_u64(data, 8);
        test_function221(_param0 ,_param1);
    });
}
