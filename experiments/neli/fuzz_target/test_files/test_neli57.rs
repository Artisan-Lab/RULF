#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function57(_param0 :u8) {
    let _local0 = <neli::rtnl::RtgenmsgBuilder as std::default::Default>::default();
    let _local1 = <neli::consts::rtnl::RtAddrFamily as std::convert::From::<u8>>::from(_param0);
    let _ = neli::rtnl::RtgenmsgBuilder::rtgen_family(_local0, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function57(_param0);
    });
}
