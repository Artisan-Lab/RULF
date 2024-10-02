#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect("slice with incorrect length");
    f32::from_le_bytes(data_array)
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn test_function182(_param0 :lofty::musepack::sv8::EncoderInfo ,_param1 :lofty::musepack::sv8::EncoderInfo) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <lofty::musepack::sv8::EncoderInfo as std::cmp::PartialEq::<lofty::musepack::sv8::EncoderInfo>>::eq(_local0_param0_helper1, _local0_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 16 {return;}
        let _param0 = lofty::musepack::sv8::EncoderInfo{profile: _to_f32(data, 0), pns_tool: _to_bool(data, 4), major: _to_u8(data, 5), minor: _to_u8(data, 6), build: _to_u8(data, 7)};
        let _param1 = lofty::musepack::sv8::EncoderInfo{profile: _to_f32(data, 8), pns_tool: _to_bool(data, 12), major: _to_u8(data, 13), minor: _to_u8(data, 14), build: _to_u8(data, 15)};
        test_function182(_param0 ,_param1);
    });
}
