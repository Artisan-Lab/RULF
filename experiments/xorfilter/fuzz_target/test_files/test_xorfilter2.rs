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

fn test_function2(_param0 :&str ,_param1 :xorfilter::NoHash) {
    let _local0 = <std::string::String as std::convert::From::<&str>>::from(_param0);
    let _local1: xorfilter::Xor8::<xorfilter::NoHash> = xorfilter::Xor8::<xorfilter::NoHash>::with_hasher(_param1);
    let _local2_param0_helper1 = &(_local1);
    let _local2_param1_helper1 = &(_local0);
    let _: bool = xorfilter::Xor8::<xorfilter::NoHash>::contains(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        let _param1 = xorfilter::NoHash{};
        test_function2(_param0 ,_param1);
    });
}
