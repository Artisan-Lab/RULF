#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function297(_param0 :u8) {
    let _local0 = <neli::consts::genl::CtrlCmd as std::convert::From::<u8>>::from(_param0);
    let _local1_param0_helper1 = &(_local0);
    let _ = <neli::consts::genl::CtrlCmd as neli::Size>::padded_size(_local1_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function297(_param0);
    });
}
