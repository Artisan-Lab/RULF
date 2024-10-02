#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function2(_param0 :&[u32]) {
    let mut _local0 = neli::utils::Groups::empty();
    let _local1_param0_helper1 = &mut (_local0);
    let _ = neli::utils::Groups::add_groups(_local1_param0_helper1, _param0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 4 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_slice::<u32>(data, 0 + 0 * dynamic_length, data.len());
        test_function2(_param0);
    });
}
