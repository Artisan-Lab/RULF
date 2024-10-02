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

fn test_function76(_param0 :u8 ,_param1 :u8) {
    let _local0 = monero::network::Network::from_u8(_param0);
    let _local1 = monero::network::Network::from_u8(_param1);
    let _local2_param0_helper1 = _unwrap_result(_local0);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2_param1_helper1 = _unwrap_result(_local1);
    let _local2_param1_helper2 = &(_local2_param1_helper1);
    let _ = <monero::network::Network as std::cmp::PartialEq::<monero::network::Network>>::eq(_local2_param0_helper2, _local2_param1_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_u8(data, 1);
        test_function76(_param0 ,_param1);
    });
}
