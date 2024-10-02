#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function37(_param0 :xorfilter::NoHash) {
    let _local0 = <std::vec::Vec::<u8> as std::convert::From::<xorfilter::NoHash>>::from(_param0);
    let _ = <xorfilter::NoHash as std::convert::From::<std::vec::Vec::<u8, std::alloc::Global>>>::from(_local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = xorfilter::NoHash{};
        test_function37(_param0);
    });
}
