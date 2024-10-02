#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function50(_param0 :u16) {
    let mut _local0 = std::collections::hash_map::DefaultHasher::new();
    let _local1 = tui::style::Modifier::from_bits_truncate(_param0);
    let _local2_param0_helper1 = &(_local1);
    let _local2_param1_helper1 = &mut (_local0);
    let _: () = <tui::style::Modifier as std::hash::Hash>::hash(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u16(data, 0);
        test_function50(_param0);
    });
}
