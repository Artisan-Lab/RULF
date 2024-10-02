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

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function130(_param0 :i8) {
    let _local0 = <toml::Value as std::convert::From::<i8>>::from(_param0);
    let _local1: std::result::Result::<toml::Value, toml::ser::Error> = toml::Value::try_from(_local0);
    let _local2_param0_helper1 = _unwrap_result(_local1);
    let _: toml::de::Error = <toml::de::Error as serde::de::Error>::custom(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_i8(data, 0);
        test_function130(_param0);
    });
}
