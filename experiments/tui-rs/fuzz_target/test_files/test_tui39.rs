#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function39(_param0 :&[char]) {
    let _local0 = <tui::widgets::Row::<'_> as std::default::Default>::default();
    let _local1: tui::widgets::Row::<'_> = tui::widgets::Row::<'_>::new(_param0);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _ = <tui::widgets::Row::<'_> as std::cmp::PartialEq::<tui::widgets::Row::<'_>>>::eq(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 4 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_slice::<char>(data, 0 + 0 * dynamic_length, data.len());
        test_function39(_param0);
    });
}
