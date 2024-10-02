#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _unwrap_result<T, E>(_res: Result<T, E>) -> T {
    match _res {
        Ok(_t) => _t,
        Err(_) => {
            use std::process;
            process::exit(0);
        },
    }
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function27(_param0 :u32) {
    let _local0 = <neli::rtnl::TcmsgBuilder as std::default::Default>::default();
    let _local1 = neli::rtnl::TcmsgBuilder::tcm_handle(_local0, _param0);
    let _local2 = <neli::rtnl::IfaddrmsgBuilder as std::default::Default>::default();
    let _local3 = neli::rtnl::IfaddrmsgBuilder::build(_local2);
    let _local4_param0_helper1 = _unwrap_result(_local3);
    let _local4_param0_helper2 = &(_local4_param0_helper1);
    let _local4 = neli::rtnl::Ifaddrmsg::ifa_scope(_local4_param0_helper2);
    let _local5 = <libc::c_uchar as std::convert::From::<&neli::consts::rtnl::RtScope>>::from(_local4);
    let _ = neli::rtnl::TcmsgBuilder::tcm_family(_local1, _local5);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_u32(data, 0);
        test_function27(_param0);
    });
}
