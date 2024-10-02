#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function208(_param0 :u16) {
    let _local0 = <neli::consts::rtnl::Nud as bitflags::traits::Flags>::from_bits_retain(_param0);
    let _ = <u16 as std::convert::From::<neli::consts::rtnl::Nud>>::from(_local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u16(data, 0);
        test_function208(_param0);
    });
}
