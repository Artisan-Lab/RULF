#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function58(_param0 :u8) {
    let _local0 = <neli::consts::netfilter::LogCmd as std::convert::From::<u8>>::from(_param0);
    let _local1 = <neli::consts::netfilter::LogCfgCmdWrapper as std::convert::From::<neli::consts::netfilter::LogCmd>>::from(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _ = <neli::consts::netfilter::LogCfgCmdWrapper as neli::Size>::unpadded_size(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function58(_param0);
    });
}
