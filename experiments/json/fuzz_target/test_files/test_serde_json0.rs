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

fn _to_f64(data:&[u8], index: usize) -> f64 {
    let data_slice = &data[index..index+8];
    use std::convert::TryInto;
    let data_array:[u8;8] = data_slice.try_into().expect("slice with incorrect length");
    f64::from_le_bytes(data_array)
}

fn test_function0(_param0 :f64 ,_param1 :&str) {
    let _local0 = serde_json::value::Number::from_f64(_param0);
    let _local1_param0_helper1 = _unwrap_option(_local0);
    let _local1 = <serde_json::Value as std::convert::From::<serde_json::value::Number>>::from(_local1_param0_helper1);
    let _local2_param0_helper1 = &(_local1);
    let _ = <serde_json::Value as std::cmp::PartialEq::<str>>::eq(_local2_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 9 {return;}
        let dynamic_length = (data.len() - 8) / 1;
        let _param0 = _to_f64(data, 0);
        let _param1 = _to_str(data, 8 + 0 * dynamic_length, data.len());
        test_function0(_param0 ,_param1);
    });
}
