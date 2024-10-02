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

fn _to_f64(data:&[u8], index: usize) -> f64 {
    let data_slice = &data[index..index+8];
    use std::convert::TryInto;
    let data_array:[u8;8] = data_slice.try_into().expect("slice with incorrect length");
    f64::from_le_bytes(data_array)
}

fn test_function78(_param0 :f64) {
    let _local0 = <toml::Value as std::convert::From::<f64>>::from(_param0);
    let _local1_param0_helper1 = &(_local0);
    let mut _local1: std::result::Result::<std::string::String, toml::ser::Error> = toml::ser::to_string_pretty(_local1_param0_helper1);
    let mut _local2_param0_helper1 = _unwrap_result(_local1);
    let _local2_param0_helper2 = &mut (_local2_param0_helper1);
    let _ = toml::Serializer::<'_>::new(_local2_param0_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 8 {return;}
        let _param0 = _to_f64(data, 0);
        test_function78(_param0);
    });
}
