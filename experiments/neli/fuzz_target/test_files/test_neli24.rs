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

fn test_function24(_param0 :u8 ,_param1 :u16) {
    let _local0 = <neli::consts::rtnl::RtAddrFamily as std::convert::From::<u8>>::from(_param0);
    let _local1 = <neli::rtnl::IfinfomsgBuilder as std::default::Default>::default();
    let _local2 = neli::rtnl::IfinfomsgBuilder::ifi_family(_local1, _local0);
    let _local3 = <neli::consts::rtnl::Ifa as std::convert::From::<u16>>::from(_param1);
    let _local4 = <neli::consts::rtnl::RtaTypeWrapper as std::convert::From::<neli::consts::rtnl::Ifa>>::from(_local3);
    let _local5 = <libc::c_ushort as std::convert::From::<neli::consts::rtnl::RtaTypeWrapper>>::from(_local4);
    let _local6 = <neli::consts::rtnl::Arphrd as std::convert::From::<u16>>::from(_local5);
    let _ = neli::rtnl::IfinfomsgBuilder::ifi_type(_local2, _local6);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 3 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_u16(data, 1);
        test_function24(_param0 ,_param1);
    });
}
