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

fn _unwrap_option<T>(_opt: Option<T>) -> T {
    match _opt {
        Some(_t) => _t,
        None => {
            use std::process;
            process::exit(0);
        }
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

fn test_function0(_param0 :&str) {
    let _local0 = <cookie::Cookie::<'_> as std::str::FromStr>::from_str(_param0);
    let _local1_param0_helper1 = _unwrap_result(_local0);
    let _local1_param0_helper2 = &(_local1_param0_helper1);
    let _local1 = cookie::Cookie::<'_>::same_site(_local1_param0_helper2);
    let mut _local2 = std::collections::hash_map::DefaultHasher::new();
    let _local3_param0_helper1 = _unwrap_option(_local1);
    let _local3_param0_helper2 = &(_local3_param0_helper1);
    let _local3_param1_helper1 = &mut (_local2);
    let _: () = <cookie::SameSite as std::hash::Hash>::hash(_local3_param0_helper2, _local3_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        test_function0(_param0);
    });
}
