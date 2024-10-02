#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function167(_param0 :u8 ,_param1 :u8) {
    let _local0 = <neli::consts::rtnl::Ntf as bitflags::traits::Flags>::from_bits_retain(_param0);
    let _local1 = <neli::consts::rtnl::Ntf as bitflags::traits::Flags>::from_bits_retain(_param1);
    let _ = <neli::consts::rtnl::Ntf as std::ops::BitAnd::<neli::consts::rtnl::Ntf>>::bitand(_local0, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_u8(data, 1);
        test_function167(_param0 ,_param1);
    });
}
