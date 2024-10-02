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

fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
}

fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function22(_param0 :&str ,_param1 :i64) {
    let _local0 = monero::util::amount::SignedAmount::from_str_with_denomination(_param0);
    let _local1_param0_helper1 = _unwrap_result(_local0);
    let mut _local1 = monero::util::amount::SignedAmount::checked_abs(_local1_param0_helper1);
    let mut _local2_param0_helper1 = _unwrap_option(_local1);
    let _local2_param0_helper2 = &mut (_local2_param0_helper1);
    let _ = <monero::util::amount::SignedAmount as std::ops::DivAssign::<i64>>::div_assign(_local2_param0_helper2, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 9 {return;}
        let dynamic_length = (data.len() - 8) / 1;
        let _param0 = _to_str(data, 8 + 0 * dynamic_length, data.len());
        let _param1 = _to_i64(data, 0);
        test_function22(_param0 ,_param1);
    });
}
