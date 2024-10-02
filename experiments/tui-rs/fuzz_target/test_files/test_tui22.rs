#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function22(_param0 :&[(f64 ,f64)] ,_param1 :&[(f64 ,f64)]) {
    let _local0 = <tui::widgets::Dataset::<'_> as std::default::Default>::default();
    let _local1 = tui::widgets::Dataset::<'_>::data(_local0, _param0);
    let _ = tui::widgets::Dataset::<'_>::data(_local1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 32 {return;}
        let dynamic_length = (data.len() - 0) / 2;
        let _param0 = _to_slice::<(f64 ,f64)>(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param1 = _to_slice::<(f64 ,f64)>(data, 0 + 1 * dynamic_length, data.len());
        test_function22(_param0 ,_param1);
    });
}
