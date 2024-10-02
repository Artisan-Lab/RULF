#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn test_function7(_param0 :bool ,_param1 :&[u8]) {
    let _local0_param0_helper1 = &(_param0);
    let mut _local0 = <bool as prost::Message>::encode_length_delimited_to_vec(_local0_param0_helper1);
    let _local1_param0_helper1 = &mut (_local0);
    let _: std::result::Result::<(), prost::DecodeError> = <std::vec::Vec::<u8> as prost::Message>::merge(_local1_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 1) / 1;
        let _param0 = _to_bool(data, 0);
        let _param1 = _to_slice::<u8>(data, 1 + 0 * dynamic_length, data.len());
        test_function7(_param0 ,_param1);
    });
}
