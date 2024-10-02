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

fn test_function39(_param0 :&str) {
    let _local0 = <std::vec::Vec::<u8, std::alloc::Global> as std::convert::From::<&str>>::from(_param0);
    let _local1: flate2::write::DeflateDecoder::<std::vec::Vec::<u8, std::alloc::Global>> = flate2::write::DeflateDecoder::<std::vec::Vec::<u8, std::alloc::Global>>::new(_local0);
    let _local2: flate2::write::DeflateDecoder::<flate2::write::DeflateDecoder::<std::vec::Vec::<u8, std::alloc::Global>>> = flate2::write::DeflateDecoder::<flate2::write::DeflateDecoder::<std::vec::Vec::<u8, std::alloc::Global>>>::new(_local1);
    let _: std::io::Result::<flate2::write::DeflateDecoder::<std::vec::Vec::<u8, std::alloc::Global>>> = flate2::write::DeflateDecoder::<flate2::write::DeflateDecoder::<std::vec::Vec::<u8, std::alloc::Global>>>::finish(_local2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        test_function39(_param0);
    });
}
