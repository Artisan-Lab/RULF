#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function15(_param0 :xorfilter::NoHash ,_param1 :&[u64]) {
    let mut _local0: xorfilter::Xor8::<xorfilter::NoHash> = xorfilter::Xor8::<xorfilter::NoHash>::with_hasher(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let _ = xorfilter::Xor8::<xorfilter::NoHash>::populate_keys(_local1_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 8 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = xorfilter::NoHash{};
        let _param1 = _to_slice::<u64>(data, 0 + 0 * dynamic_length, data.len());
        test_function15(_param0 ,_param1);
    });
}
