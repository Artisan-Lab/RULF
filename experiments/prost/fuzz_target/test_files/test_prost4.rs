#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect("slice with incorrect length");
    f32::from_le_bytes(data_array)
}

fn test_function4(_param0 :f32 ,_param1 :&[u8]) {
    let _local0_param0_helper1 = &(_param0);
    let mut _local0 = <f32 as prost::Message>::encode_to_vec(_local0_param0_helper1);
    let _local1_param0_helper1 = &mut (_local0);
    let _: std::result::Result::<(), prost::DecodeError> = <std::vec::Vec::<u8> as prost::Message>::merge(_local1_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 5 {return;}
        let dynamic_length = (data.len() - 4) / 1;
        let _param0 = _to_f32(data, 0);
        let _param1 = _to_slice::<u8>(data, 4 + 0 * dynamic_length, data.len());
        test_function4(_param0 ,_param1);
    });
}
