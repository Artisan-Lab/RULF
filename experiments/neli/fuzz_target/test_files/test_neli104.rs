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

fn test_function104(_param0 :u16) {
    let _local0 = <neli::consts::genl::CtrlAttr as std::convert::From::<u16>>::from(_param0);
    let _local1 = <neli::consts::genl::NlAttrTypeWrapper as std::convert::From::<neli::consts::genl::CtrlAttr>>::from(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _ = <neli::consts::genl::NlAttrTypeWrapper as neli::Size>::unpadded_size(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u16(data, 0);
        test_function104(_param0);
    });
}
