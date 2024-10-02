#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function15(_param0 :&[u32]) {
    let _local0 = neli::utils::Groups::new_groups(_param0);
    let _local1_param0_helper1 = &(_local0);
    let _ = neli::utils::Groups::as_bitmask(_local1_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 4 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_slice::<u32>(data, 0 + 0 * dynamic_length, data.len());
        test_function15(_param0);
    });
}
