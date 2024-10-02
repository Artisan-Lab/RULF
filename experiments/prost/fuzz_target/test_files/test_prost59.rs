#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_f64(data:&[u8], index: usize) -> f64 {
    let data_slice = &data[index..index+8];
    use std::convert::TryInto;
    let data_array:[u8;8] = data_slice.try_into().expect("slice with incorrect length");
    f64::from_le_bytes(data_array)
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function59(mut _param0 :f64 ,_param1 :&[u8]) {
    let _local0_param0_helper1 = &mut (_param0);
    let _: std::result::Result::<(), prost::DecodeError> = <f64 as prost::Message>::merge(_local0_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 9 {return;}
        let dynamic_length = (data.len() - 8) / 1;
        let _param0 = _to_f64(data, 0);
        let _param1 = _to_slice::<u8>(data, 8 + 0 * dynamic_length, data.len());
        test_function59(_param0 ,_param1);
    });
}
