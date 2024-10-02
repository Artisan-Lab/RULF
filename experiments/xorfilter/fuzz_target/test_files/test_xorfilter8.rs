#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function8(_param0 :&[u8]) {
    let _local0 = <xorfilter::BuildHasherDefault as std::default::Default>::default();
    let mut _local1: xorfilter::Xor8::<xorfilter::BuildHasherDefault> = xorfilter::Xor8::<xorfilter::BuildHasherDefault>::with_hasher(_local0);
    let _local2_param0_helper1 = &mut (_local1);
    let _ = xorfilter::Xor8::<xorfilter::BuildHasherDefault>::populate(_local2_param0_helper1, _param0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_slice::<u8>(data, 0 + 0 * dynamic_length, data.len());
        test_function8(_param0);
    });
}
