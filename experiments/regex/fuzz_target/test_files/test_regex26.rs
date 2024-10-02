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

use regex::bytes::Replacer;

fn test_function26(mut _param0 :regex::bytes::NoExpand ,_param1 :&str ,_param2 :&[u8]) {
    let _local0_param0_helper1 = &mut (_param0);
    let _local0 = <regex::bytes::NoExpand<'_> as regex::bytes::Replacer>::no_expansion(_local0_param0_helper1);
    let _local1 = regex::bytes::Regex::new(_param1);
    let _local2_param0_helper1 = _unwrap_result(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2_param2_helper1 = _unwrap_option(_local0);
    let _: std::borrow::Cow<'_, [u8]> = regex::bytes::Regex::replace_all(_local2_param0_helper2, _param2, _local2_param2_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 3 {return;}
        let dynamic_length = (data.len() - 1) / 3;
        let _param0 = regex::bytes::NoExpand(_to_slice::<u8>(data, 1 + 0 * dynamic_length, 1 + 1 * dynamic_length));
        let _param1 = _to_str(data, 1 + 1 * dynamic_length, 1 + 2 * dynamic_length);
        let _param2 = _to_slice::<u8>(data, 1 + 2 * dynamic_length, data.len());
        test_function26(_param0 ,_param1 ,_param2);
    });
}
