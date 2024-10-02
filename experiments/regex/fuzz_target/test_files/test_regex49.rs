#[macro_use]
extern crate afl;
extern crate regex;
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

fn test_function49(_param0 :&str) {
    let mut _local0 = regex::escape(_param0);
    let mut _local1_param0_helper1 = &(_local0);
    let _local1_param0_helper2 = &mut (_local1_param0_helper1);
    let mut _local1 = <&std::string::String as regex::Replacer>::by_ref(_local1_param0_helper2);
    let _local2_param0_helper1 = &mut (_local1);
    let _: core::option::Option<std::borrow::Cow<'_, str>> = <regex::ReplacerRef<'_, &std::string::String> as regex::Replacer>::no_expansion(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        test_function49(_param0);
    });
}
