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

fn test_function113(_param0 :u32) {
    let _local0 = lofty::iff::wav::RIFFInfoList::new();
    let mut _local1 = <lofty::Tag as std::convert::From::<lofty::iff::wav::RIFFInfoList>>::from(_local0);
    let _local2_param0_helper1 = &mut (_local1);
    let _ = <lofty::Tag as lofty::Accessor>::set_year(_local2_param0_helper1, _param0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_u32(data, 0);
        test_function113(_param0);
    });
}
