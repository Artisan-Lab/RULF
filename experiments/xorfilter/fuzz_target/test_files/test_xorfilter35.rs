#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function35(_param0 :xorfilter::NoHash ,_param1 :xorfilter::NoHash) {
    let _local0: xorfilter::Xor8::<xorfilter::NoHash> = xorfilter::Xor8::<xorfilter::NoHash>::with_hasher(_param0);
    let _local1: xorfilter::Xor8::<xorfilter::NoHash> = xorfilter::Xor8::<xorfilter::NoHash>::with_hasher(_param1);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _: bool = <xorfilter::Xor8::<xorfilter::NoHash> as std::cmp::PartialEq::<xorfilter::Xor8::<xorfilter::NoHash>>>::eq(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = xorfilter::NoHash{};
        let _param1 = xorfilter::NoHash{};
        test_function35(_param0 ,_param1);
    });
}
