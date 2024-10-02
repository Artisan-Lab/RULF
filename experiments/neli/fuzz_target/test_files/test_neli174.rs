#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function174(_param0 :u8 ,_param1 :u8) {
    let _local0 = <neli::consts::netfilter::LogCmd as std::convert::From::<u8>>::from(_param0);
    let _local1 = <neli::consts::netfilter::LogCmd as std::convert::From::<u8>>::from(_param1);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _ = <neli::consts::netfilter::LogCmd as std::cmp::PartialEq::<neli::consts::netfilter::LogCmd>>::eq(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_u8(data, 1);
        test_function174(_param0 ,_param1);
    });
}
