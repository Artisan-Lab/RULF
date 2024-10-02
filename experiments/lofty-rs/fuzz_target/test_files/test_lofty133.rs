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

fn _to_u64(data:&[u8], index:usize)->u64 {
    let data0 = _to_u32(data, index) as u64;
    let data1 = _to_u32(data, index+4) as u64;
    data0 << 32 | data1
}

fn _to_usize(data:&[u8], index:usize)->usize {
    _to_u64(data, index) as usize
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn test_function133(_param0 :usize ,_param1 :u8) {
    let _local0 = lofty::iff::aiff::AIFFTextChunks::new();
    let mut _local1 = <lofty::Tag as std::convert::From::<lofty::iff::aiff::AIFFTextChunks>>::from(_local0);
    let _local2_param0_helper1 = &mut (_local1);
    let mut _local2 = lofty::Tag::remove_picture(_local2_param0_helper1, _param0);
    let _local3 = lofty::PictureType::from_u8(_param1);
    let _local4_param0_helper1 = &mut (_local2);
    let _ = lofty::Picture::set_pic_type(_local4_param0_helper1, _local3);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 9 {return;}
        let _param0 = _to_usize(data, 0);
        let _param1 = _to_u8(data, 8);
        test_function133(_param0 ,_param1);
    });
}
