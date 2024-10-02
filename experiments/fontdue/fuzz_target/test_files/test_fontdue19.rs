#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect("slice with incorrect length");
    f32::from_le_bytes(data_array)
}

fn test_function19(_param0 :fontdue::OutlineBounds ,_param1 :f32) {
    let _local0_param0_helper1 = &(_param0);
    let _ = fontdue::OutlineBounds::scale(_local0_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 20 {return;}
        let _param0 = fontdue::OutlineBounds{xmin: _to_f32(data, 0), ymin: _to_f32(data, 4), width: _to_f32(data, 8), height: _to_f32(data, 12)};
        let _param1 = _to_f32(data, 16);
        test_function19(_param0 ,_param1);
    });
}
