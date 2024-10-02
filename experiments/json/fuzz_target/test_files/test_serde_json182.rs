#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function182(_param0 :serde_json::value::Serializer ,_param1 :&[u8]) {
    let _ = <serde_json::value::Serializer as serde::ser::Serializer>::serialize_bytes(_param0, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = serde_json::value::Serializer{};
        let _param1 = _to_slice::<u8>(data, 0 + 0 * dynamic_length, data.len());
        test_function182(_param0 ,_param1);
    });
}
