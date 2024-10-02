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

fn test_function120(_param0 :u8) {
    let _local0 = <toml::Value as std::convert::From::<u8>>::from(_param0);
    let _local1: std::result::Result::<toml::Value, toml::ser::Error> = toml::Value::try_from(_local0);
    let _local2_param0_helper1 = _unwrap_result(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _: std::result::Result::<std::string::String, toml::ser::Error> = toml::ser::to_string_pretty(_local2_param0_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function120(_param0);
    });
}
