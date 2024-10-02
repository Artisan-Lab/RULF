#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _unwrap_option<T>(_opt: Option<T>) -> T {
    match _opt {
        Some(_t) => _t,
        None => {
            use std::process;
            process::exit(0);
        }
    }
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function35(_param0 :&[u8] ,_param1 :&[u8]) {
    let _local0 = lofty::FileType::from_buffer(_param0);
    let _local1 = lofty::FileType::from_buffer(_param1);
    let _local2_param0_helper1 = _unwrap_option(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2 = lofty::FileType::primary_tag_type(_local2_param0_helper2);
    let _local3_param0_helper1 = _unwrap_option(_local0);
    let _local3_param0_helper2 = &(_local3_param0_helper1);
    let _ = lofty::FileType::supports_tag_type(_local3_param0_helper2, _local2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 0) / 2;
        let _param0 = _to_slice::<u8>(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param1 = _to_slice::<u8>(data, 0 + 1 * dynamic_length, data.len());
        test_function35(_param0 ,_param1);
    });
}
