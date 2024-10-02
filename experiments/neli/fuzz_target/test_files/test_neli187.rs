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

fn test_function187(_param0 :u16 ,_param1 :u16) {
    let _local0 = <neli::consts::rtnl::Ifa as std::convert::From::<u16>>::from(_param0);
    let _local1 = <neli::consts::rtnl::RtaTypeWrapper as std::convert::From::<neli::consts::rtnl::Ifa>>::from(_local0);
    let _local2 = <libc::c_ushort as std::convert::From::<neli::consts::rtnl::RtaTypeWrapper>>::from(_local1);
    let _local3 = <neli::consts::rtnl::Tca as std::convert::From::<u16>>::from(_local2);
    let _local4 = <neli::consts::rtnl::Ifa as std::convert::From::<u16>>::from(_param1);
    let _local5 = <neli::consts::rtnl::RtaTypeWrapper as std::convert::From::<neli::consts::rtnl::Ifa>>::from(_local4);
    let _local6 = <libc::c_ushort as std::convert::From::<neli::consts::rtnl::RtaTypeWrapper>>::from(_local5);
    let _local7 = <neli::consts::rtnl::Tca as std::convert::From::<u16>>::from(_local6);
    let _local8_param0_helper1 = &(_local3);
    let _local8_param1_helper1 = &(_local7);
    let _ = <neli::consts::rtnl::Tca as std::cmp::PartialEq::<neli::consts::rtnl::Tca>>::eq(_local8_param0_helper1, _local8_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_u16(data, 0);
        let _param1 = _to_u16(data, 2);
        test_function187(_param0 ,_param1);
    });
}
