#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function32(_param0 :xorfilter::NoHash) {
    let _local0 = <std::vec::Vec::<u8> as std::convert::From::<xorfilter::NoHash>>::from(_param0);
    let _local1 = <xorfilter::BuildHasherDefault as std::convert::From::<std::vec::Vec::<u8, std::alloc::Global>>>::from(_local0);
    let _ = <std::vec::Vec::<u8> as std::convert::From::<xorfilter::BuildHasherDefault>>::from(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = xorfilter::NoHash{};
        test_function32(_param0);
    });
}
