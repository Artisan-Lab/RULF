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

fn test_function63(_param0 :u8) {
    let _local0 = <neli::consts::rtnl::RtAddrFamily as std::convert::From::<u8>>::from(_param0);
    let _local1 = <neli::rtnl::IfaddrmsgBuilder as std::default::Default>::default();
    let _local2 = neli::rtnl::IfaddrmsgBuilder::ifa_family(_local1, _local0);
    let _local3 = <neli::rtnl::IfaddrmsgBuilder as std::default::Default>::default();
    let _local4 = neli::rtnl::IfaddrmsgBuilder::build(_local3);
    let _local5_param0_helper1 = _unwrap_result(_local4);
    let _local5_param0_helper2 = &(_local5_param0_helper1);
    let _local5 = neli::rtnl::Ifaddrmsg::ifa_scope(_local5_param0_helper2);
    let _local6 = <libc::c_uchar as std::convert::From::<&neli::consts::rtnl::RtScope>>::from(_local5);
    let _ = neli::rtnl::IfaddrmsgBuilder::ifa_prefixlen(_local2, _local6);
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
    if data.len() != 1 {return;}
    let _param0 = _to_u8(data, 0);
    test_function63(_param0);

}