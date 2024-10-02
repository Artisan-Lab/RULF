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

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function25(_param0 :u16) {
    let _local0 = <neli::consts::rtnl::Nud as bitflags::traits::Flags>::from_bits_retain(_param0);
    let _local1 = <neli::rtnl::NdmsgBuilder as std::default::Default>::default();
    let _local2 = neli::rtnl::NdmsgBuilder::ndm_state(_local1, _local0);
    let _local3 = <neli::rtnl::IfaddrmsgBuilder as std::default::Default>::default();
    let _local4 = neli::rtnl::IfaddrmsgBuilder::build(_local3);
    let _local5_param0_helper1 = _unwrap_result(_local4);
    let _local5_param0_helper2 = &(_local5_param0_helper1);
    let _local5 = neli::rtnl::Ifaddrmsg::ifa_scope(_local5_param0_helper2);
    let _local6 = <libc::c_uchar as std::convert::From::<&neli::consts::rtnl::RtScope>>::from(_local5);
    let _local7 = <neli::consts::rtnl::Rtn as std::convert::From::<u8>>::from(_local6);
    let _ = neli::rtnl::NdmsgBuilder::ndm_type(_local2, _local7);
}

fn _read_data()-> Vec<u8> {
    use std::env;
    use std::process::exit;
    let args:Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("No crash filename provided");
        exit(-1);
    }
    use std::path::PathBuf;
    let crash_file_name = &args[1];
    let crash_path = PathBuf::from(crash_file_name);
    if !crash_path.is_file() {
        println!("Not a valid crash file");
        exit(-1);
    }
    use std::fs;
    let data =  fs::read(crash_path).unwrap();
    data
}

fn main() {
    let _content = _read_data();
    let data = &_content;
    println!("data = {:?}", data);
    println!("data len = {:?}", data.len());
    //actual body emit
    if data.len() != 2 {return;}
    let _param0 = _to_u16(data, 0);
    test_function25(_param0);

}