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

fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect("slice with incorrect length");
    f32::from_le_bytes(data_array)
}

fn test_function145(_param0 :&str ,_param1 :f32) {
    let _local0 = <serde_json::Value as std::convert::From::<&str>>::from(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let _local1_param0_helper2 = &(_local1_param0_helper1);
    let _local1_param1_helper1 = &(_param1);
    let _ = <&mut serde_json::Value as std::cmp::PartialEq::<f32>>::eq(_local1_param0_helper2, _local1_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 5 {return;}
        let dynamic_length = (data.len() - 4) / 1;
        let _param0 = _to_str(data, 4 + 0 * dynamic_length, data.len());
        let _param1 = _to_f32(data, 0);
        test_function145(_param0 ,_param1);
    });
}
