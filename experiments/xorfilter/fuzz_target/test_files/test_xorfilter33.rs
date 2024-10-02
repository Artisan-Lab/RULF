#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function33(_param0 :xorfilter::NoHash) {
    let _local0: xorfilter::Xor8::<xorfilter::NoHash> = xorfilter::Xor8::<xorfilter::NoHash>::with_hasher(_param0);
    let _local1_param0_helper1 = &(_local0);
    let _local1: std::vec::Vec::<u8> = xorfilter::Xor8::<xorfilter::NoHash>::to_bytes(_local1_param0_helper1);
    let _ = <xorfilter::NoHash as std::convert::From::<std::vec::Vec::<u8, std::alloc::Global>>>::from(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = xorfilter::NoHash{};
        test_function33(_param0);
    });
}
