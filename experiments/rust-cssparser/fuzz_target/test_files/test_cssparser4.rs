#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
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

fn test_function4(_param0 :u8 ,_param1 :&str) {
    let _local0_param0_helper1 = &(_param0);
    let _local0 = <u8 as cssparser::ToCss>::to_css_string(_local0_param0_helper1);
    let _local1 = <cssparser::CowRcStr::<'_> as std::convert::From::<std::string::String>>::from(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _: std::option::Option::<std::cmp::Ordering> = <cssparser::CowRcStr::<'_> as std::cmp::PartialOrd::<str>>::partial_cmp(_local2_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 1) / 1;
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_str(data, 1 + 0 * dynamic_length, data.len());
        test_function4(_param0 ,_param1);
    });
}
