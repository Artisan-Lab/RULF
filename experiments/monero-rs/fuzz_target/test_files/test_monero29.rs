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

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function29(_param0 :u8 ,_param1 :&[u8] ,_param2 :&[u8]) {
    let _local0 = monero::network::Network::from_u8(_param0);
    let _local1 = monero::util::key::PublicKey::from_slice(_param1);
    let _local2 = monero::util::key::PublicKey::from_slice(_param2);
    let _local3_param0_helper1 = _unwrap_result(_local0);
    let _local3_param1_helper1 = _unwrap_result(_local1);
    let _local3_param2_helper1 = _unwrap_result(_local2);
    let _ = monero::util::address::Address::subaddress(_local3_param0_helper1, _local3_param1_helper1, _local3_param2_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 3 {return;}
        let dynamic_length = (data.len() - 1) / 2;
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_slice::<u8>(data, 1 + 0 * dynamic_length, 1 + 1 * dynamic_length);
        let _param2 = _to_slice::<u8>(data, 1 + 1 * dynamic_length, data.len());
        test_function29(_param0 ,_param1 ,_param2);
    });
}
