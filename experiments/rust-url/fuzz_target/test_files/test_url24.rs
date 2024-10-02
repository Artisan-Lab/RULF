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

fn test_function24(_param0 :&str) {
    let _local0 = url::Url::parse(_param0);
    let _local1 = url::Url::options();
    let _local2_param1_helper1 = _unwrap_result(_local0);
    let _local2_param1_helper2 = &(_local2_param1_helper1);
    let _local2_param1_helper3 = Some(_local2_param1_helper2);
    let _ = url::ParseOptions::<'_>::base_url(_local1, _local2_param1_helper3);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        test_function24(_param0);
    });
}
