#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function114(_param0 :u8 ,_param1 :u8) {
    let _local0 = lofty::id3::v2::EventType::from_u8(_param0);
    let _local1 = lofty::id3::v2::EventType::from_u8(_param1);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _ = <lofty::id3::v2::EventType as std::cmp::PartialEq::<lofty::id3::v2::EventType>>::eq(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_u8(data, 1);
        test_function114(_param0 ,_param1);
    });
}
