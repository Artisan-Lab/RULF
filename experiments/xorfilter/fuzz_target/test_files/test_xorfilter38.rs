#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function38(_param0 :xorfilter::NoHash) {
    let mut _local0: xorfilter::Xor8::<xorfilter::NoHash> = xorfilter::Xor8::<xorfilter::NoHash>::with_hasher(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let _: xorfilter::Result::<()> = xorfilter::Xor8::<xorfilter::NoHash>::build(_local1_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = xorfilter::NoHash{};
        test_function38(_param0);
    });
}
