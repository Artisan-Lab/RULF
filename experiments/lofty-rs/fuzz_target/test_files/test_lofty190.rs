#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn test_function190(_param0 :lofty::id3::v2::AudioTextFrameFlags) {
    let _local0_param0_helper1 = &(_param0);
    let _ = lofty::id3::v2::AudioTextFrameFlags::as_u8(_local0_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = lofty::id3::v2::AudioTextFrameFlags{scrambling: _to_bool(data, 0)};
        test_function190(_param0);
    });
}
