#[macro_use]
extern crate afl;
extern crate regex;
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

fn test_function38(mut _param0 :regex::NoExpand) {
    let _local0_param0_helper1 = &mut (_param0);
    let mut _local0 = <regex::NoExpand<'_> as regex::Replacer>::by_ref(_local0_param0_helper1);
    let _local1_param0_helper1 = &mut (_local0);
    let mut _local1: core::option::Option<std::borrow::Cow<'_, str>> = <regex::ReplacerRef<'_, regex::NoExpand<'_>> as regex::Replacer>::no_expansion(_local1_param0_helper1);
    let mut _local2_param0_helper1 = _unwrap_option(_local1);
    let _local2_param0_helper2 = &mut (_local2_param0_helper1);
    let _ = <std::borrow::Cow<'_, str> as regex::Replacer>::no_expansion(_local2_param0_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 1) / 1;
        let _param0 = regex::NoExpand(_to_str(data, 1 + 0 * dynamic_length, data.len()));
        test_function38(_param0);
    });
}
