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

fn test_function24(_param0 :&str ,_param1 :&str) {
    let mut _local0 = cssparser::ParserInput::<'_>::new(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let _local1 = cssparser::Parser::<'_, '_>::new(_local1_param0_helper1);
    let mut _local2 = cssparser::ParserInput::<'_>::new(_param1);
    let _local3_param0_helper1 = &mut (_local2);
    let _local3 = cssparser::Parser::<'_, '_>::new(_local3_param0_helper1);
    let _local4_param0_helper1 = &(_local3);
    let _local4 = cssparser::Parser::<'_, '_>::position(_local4_param0_helper1);
    let _local5_param0_helper1 = &(_local1);
    let _ = cssparser::Parser::<'_, '_>::slice_from(_local5_param0_helper1, _local4);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 0) / 2;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param1 = _to_str(data, 0 + 1 * dynamic_length, data.len());
        test_function24(_param0 ,_param1);
    });
}
