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

fn _to_str(data:&[u8], start_index: usize, end_index: usize)->&str {
    let data_slice = &data[start_index..end_index];
    use std::str;
    match str::from_utf8(data_slice) {
        Ok(s)=>s,
        Err(_)=>{
            use std::process;
            process::exit(0);
        }
    }
}

fn test_function54(_param0 :&str) {
    let _local0 = <toml::Value as std::convert::From::<&str>>::from(_param0);
    let mut _local1: std::result::Result::<toml::map::Map::<std::string::String, toml::Value>, toml::ser::Error> = toml::map::Map::<std::string::String, toml::Value>::try_from(_local0);
    let mut _local2_param0_helper1 = _unwrap_result(_local1);
    let _local2_param0_helper2 = &mut (_local2_param0_helper1);
    let _ = toml::map::Map::<std::string::String, toml::Value>::iter_mut(_local2_param0_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        test_function54(_param0);
    });
}
