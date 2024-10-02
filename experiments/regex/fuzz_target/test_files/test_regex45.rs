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

use regex::Replacer;

fn test_function45(_param0 :&str ,mut _param1 :regex::NoExpand ,_param2 :&str) {
    let _local0 = regex::Regex::new(_param0);
    let _local1_param0_helper1 = &mut (_param1);
    let mut _local1 = <regex::NoExpand<'_> as regex::Replacer>::no_expansion(_local1_param0_helper1);
    let mut _local2_param0_helper1 = _unwrap_option(_local1);
    let _local2_param0_helper2 = &mut (_local2_param0_helper1);
    let _local2 = <std::borrow::Cow<'_, str> as regex::Replacer>::by_ref(_local2_param0_helper2);
    let _local3_param0_helper1 = _unwrap_result(_local0);
    let _local3_param0_helper2 = &(_local3_param0_helper1);
    let _: std::borrow::Cow<'_, str> = regex::Regex::replace_all(_local3_param0_helper2, _param2, _local2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 3 {return;}
        let dynamic_length = (data.len() - 1) / 3;
        let _param0 = _to_str(data, 1 + 0 * dynamic_length, 1 + 1 * dynamic_length);
        let _param1 = regex::NoExpand(_to_str(data, 1 + 1 * dynamic_length, 1 + 2 * dynamic_length));
        let _param2 = _to_str(data, 1 + 2 * dynamic_length, data.len());
        test_function45(_param0 ,_param1 ,_param2);
    });
}
