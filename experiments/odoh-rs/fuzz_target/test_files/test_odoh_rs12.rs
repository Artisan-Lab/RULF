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

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function12(_param0 :u16 ,_param1 :u16 ,_param2 :u16 ,_param3 :&[u8] ,mut _param4 :&[u8]) {
    let _local0 = odoh_rs::ObliviousDoHKeyPair::from_parameters(_param0, _param1, _param2, _param3);
    let _local1_param0_helper1 = &mut (_param4);
    let _local1: std::result::Result::<odoh_rs::ObliviousDoHMessage, odoh_rs::Error> = <odoh_rs::ObliviousDoHMessage as odoh_rs::Deserialize>::deserialize(_local1_param0_helper1);
    let _local2_param0_helper1 = _unwrap_result(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2_param1_helper1 = &(_local0);
    let _ = odoh_rs::decrypt_query(_local2_param0_helper2, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 8 {return;}
        let dynamic_length = (data.len() - 6) / 2;
        let _param0 = _to_u16(data, 0);
        let _param1 = _to_u16(data, 2);
        let _param2 = _to_u16(data, 4);
        let _param3 = _to_slice::<u8>(data, 6 + 0 * dynamic_length, 6 + 1 * dynamic_length);
        let _param4 = _to_slice::<u8>(data, 6 + 1 * dynamic_length, data.len());
        test_function12(_param0 ,_param1 ,_param2 ,_param3 ,_param4);
    });
}
