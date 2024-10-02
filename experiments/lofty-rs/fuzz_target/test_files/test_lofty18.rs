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

fn test_function18(_param0 :&[u8] ,_param1 :bool) {
    let _local0 = <lofty::ParsingMode as std::default::Default>::default();
    let _ = lofty::Picture::from_flac_bytes(_param0, _param1, _local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 1) / 1;
        let _param0 = _to_slice::<u8>(data, 1 + 0 * dynamic_length, data.len());
        let _param1 = _to_bool(data, 0);
        test_function18(_param0 ,_param1);
    });
}
