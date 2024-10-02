#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function54(_param0 :xorfilter::NoHash) {
    let _local0_param0_helper1 = &(_param0);
    let _ = <xorfilter::NoHash as std::hash::Hasher>::finish(_local0_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = xorfilter::NoHash{};
        test_function54(_param0);
    });
}
