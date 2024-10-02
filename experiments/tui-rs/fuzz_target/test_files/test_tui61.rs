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

fn test_function61(_param0 :f64 ,_param1 :f64) {
    let _local0 = <tui::widgets::LineGauge::<'_> as std::default::Default>::default();
    let _local1 = tui::widgets::LineGauge::<'_>::ratio(_local0, _param0);
    let _ = tui::widgets::LineGauge::<'_>::ratio(_local1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 16 {return;}
        let _param0 = _to_f64(data, 0);
        let _param1 = _to_f64(data, 8);
        test_function61(_param0 ,_param1);
    });
}
