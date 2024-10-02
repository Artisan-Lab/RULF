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

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function13(_param0 :i16 ,_param1 :&str) {
    let _local0 = <serde_json::value::Number as std::convert::From::<i16>>::from(_param0);
    let _local1 = <serde_json::Value as std::convert::From::<serde_json::value::Number>>::from(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _local2_param1_helper1 = &(_param1);
    let _ = <serde_json::Value as std::cmp::PartialEq::<&str>>::eq(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 3 {return;}
        let dynamic_length = (data.len() - 2) / 1;
        let _param0 = _to_i16(data, 0);
        let _param1 = _to_str(data, 2 + 0 * dynamic_length, data.len());
        test_function13(_param0 ,_param1);
    });
}
