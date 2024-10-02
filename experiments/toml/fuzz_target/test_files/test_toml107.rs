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

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn test_function107(_param0 :bool) {
    let _local0 = <toml::Value as std::convert::From::<bool>>::from(_param0);
    let _local1_param0_helper1 = &(_local0);
    let _local1: std::result::Result::<std::string::String, toml::ser::Error> = toml::ser::to_string(_local1_param0_helper1);
    let _local2_param0_helper1 = _unwrap_result(_local1);
    let _ = <toml::Value as std::convert::From::<std::string::String>>::from(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_bool(data, 0);
        test_function107(_param0);
    });
}
