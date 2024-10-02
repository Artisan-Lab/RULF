#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _unwrap_option<T>(_opt: Option<T>) -> T {
    match _opt {
        Some(_t) => _t,
        None => {
            use std::process;
            process::exit(0);
        }
    }
}

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
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

fn test_function80(_param0 :&[u8] ,_param1 :usize ,_param2 :usize) {
    let _local0 = lofty::FileType::from_buffer(_param0);
    let _local1_param0_helper1 = _unwrap_option(_local0);
    let _local1_param0_helper2 = &(_local1_param0_helper1);
    let _local1 = lofty::FileType::primary_tag_type(_local1_param0_helper2);
    let mut _local2 = lofty::Tag::new(_local1);
    let _local3 = lofty::iff::aiff::AIFFTextChunks::new();
    let mut _local4 = <lofty::Tag as std::convert::From::<lofty::iff::aiff::AIFFTextChunks>>::from(_local3);
    let _local5_param0_helper1 = &mut (_local4);
    let _local5 = lofty::Tag::remove_picture(_local5_param0_helper1, _param1);
    let _local6_param0_helper1 = &mut (_local2);
    let _ = lofty::Tag::set_picture(_local6_param0_helper1, _param2, _local5);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 17 {return;}
        let dynamic_length = (data.len() - 16) / 1;
        let _param0 = _to_slice::<u8>(data, 16 + 0 * dynamic_length, data.len());
        let _param1 = _to_usize(data, 0);
        let _param2 = _to_usize(data, 8);
        test_function80(_param0 ,_param1 ,_param2);
    });
}
