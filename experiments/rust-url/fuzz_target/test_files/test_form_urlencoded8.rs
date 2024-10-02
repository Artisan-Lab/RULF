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

fn test_function8(_param0 :&str ,_param1 :&str) {
    let mut _local0 = <std::string::String as std::convert::From::<&str>>::from(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let mut _local1: form_urlencoded::Serializer::<'_, &mut std::string::String> = form_urlencoded::Serializer::<'_, &mut std::string::String>::new(_local1_param0_helper1);
    let _local2_param0_helper1 = &mut (_local1);
    let _: &mut form_urlencoded::Serializer::<'_, &mut std::string::String> = form_urlencoded::Serializer::<'_, &mut std::string::String>::append_key_only(_local2_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 0) / 2;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param1 = _to_str(data, 0 + 1 * dynamic_length, data.len());
        test_function8(_param0 ,_param1);
    });
}
