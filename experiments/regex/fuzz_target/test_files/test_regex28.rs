#[macro_use]
extern crate afl;
extern crate regex;
fn _unwrap_result<T, E>(_res: Result<T, E>) -> T {
    match _res {
        Ok(_t) => _t,
        Err(_) => {
            use std::process;
            process::exit(0);
        },
    }
}

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

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

use regex::bytes::Replacer;

fn test_function28(mut _param0 :regex::bytes::NoExpand ,_param1 :&str ,_param2 :&[u8] ,_param3 :usize) {
    let _local0_param0_helper1 = &mut (_param0);
    let _local0 = <regex::bytes::NoExpand<'_> as regex::bytes::Replacer>::no_expansion(_local0_param0_helper1);
    let _local1 = regex::bytes::Regex::new(_param1);
    let _local2_param0_helper1 = _unwrap_result(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2_param3_helper1 = _unwrap_option(_local0);
    let _: std::borrow::Cow<'_, [u8]> = regex::bytes::Regex::replacen(_local2_param0_helper2, _param2, _param3, _local2_param3_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 11 {return;}
        let dynamic_length = (data.len() - 9) / 3;
        let _param0 = regex::bytes::NoExpand(_to_slice::<u8>(data, 9 + 0 * dynamic_length, 9 + 1 * dynamic_length));
        let _param1 = _to_str(data, 9 + 1 * dynamic_length, 9 + 2 * dynamic_length);
        let _param2 = _to_slice::<u8>(data, 9 + 2 * dynamic_length, data.len());
        let _param3 = _to_usize(data, 1);
        test_function28(_param0 ,_param1 ,_param2 ,_param3);
    });
}
