#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function150(_param0 :u32) {
    let mut _local0 = lofty::mp4::Ilst::new();
    let _local1_param0_helper1 = &mut (_local0);
    let _ = <lofty::mp4::Ilst as lofty::Accessor>::set_track_total(_local1_param0_helper1, _param0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_u32(data, 0);
        test_function150(_param0);
    });
}
