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

fn test_function12(_param0 :xorfilter::NoHash ,_param1 :&str) {
    let _local0 = <std::vec::Vec::<u8> as std::convert::From::<xorfilter::NoHash>>::from(_param0);
    let _local1 = <xorfilter::BuildHasherDefault as std::convert::From::<std::vec::Vec::<u8, std::alloc::Global>>>::from(_local0);
    let mut _local2: xorfilter::Xor8::<xorfilter::BuildHasherDefault> = xorfilter::Xor8::<xorfilter::BuildHasherDefault>::with_hasher(_local1);
    let _local3 = <std::string::String as std::convert::From::<&str>>::from(_param1);
    let _local4_param0_helper1 = &mut (_local2);
    let _local4_param1_helper1 = &(_local3);
    let _ = xorfilter::Xor8::<xorfilter::BuildHasherDefault>::insert(_local4_param0_helper1, _local4_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = xorfilter::NoHash{};
        let _param1 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        test_function12(_param0 ,_param1);
    });
}
