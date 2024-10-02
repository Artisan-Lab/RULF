#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
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

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function80(_param0 :&str ,_param1 :u8) {
    let mut _local0 = <std::string::String as std::convert::From::<&str>>::from(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let mut _local1: cssparser::CssStringWriter::<'_, std::string::String> = cssparser::CssStringWriter::<'_, std::string::String>::new(_local1_param0_helper1);
    let _local2_param0_helper1 = &(_param1);
    let _local2_param1_helper1 = &mut (_local1);
    let _: std::fmt::Result = <u8 as cssparser::ToCss>::to_css(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 1) / 1;
        let _param0 = _to_str(data, 1 + 0 * dynamic_length, data.len());
        let _param1 = _to_u8(data, 0);
        test_function80(_param0 ,_param1);
    });
}
