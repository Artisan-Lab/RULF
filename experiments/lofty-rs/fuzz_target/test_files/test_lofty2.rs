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

fn _to_str(data:&[u8], start_index: usize, end_index: usize)->&str {
    let data_slice = &data[start_index..end_index];
    use std::str;
    match str::from_utf8(data_slice) {
        Ok(s)=>s,
        Err(_)=>{
            use std::process;
            process::exit(0);
        }
    }
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function2(_param0 :&[u8] ,_param1 :&[u8] ,_param2 :&str ,_param3 :&str) {
    let _local0 = lofty::FileType::from_buffer(_param0);
    let _local1_param0_helper1 = _unwrap_option(_local0);
    let _local1_param0_helper2 = &(_local1_param0_helper1);
    let _local1 = lofty::FileType::primary_tag_type(_local1_param0_helper2);
    let mut _local2 = lofty::Tag::new(_local1);
    let _local3 = lofty::FileType::from_buffer(_param1);
    let _local4_param0_helper1 = _unwrap_option(_local3);
    let _local4_param0_helper2 = &(_local4_param0_helper1);
    let _local4 = lofty::FileType::primary_tag_type(_local4_param0_helper2);
    let _local5 = lofty::ItemKey::from_key(_local4, _param2);
    let mut _local6 = lofty::iff::wav::RIFFInfoList::new();
    let _local7_param0_helper1 = &mut (_local6);
    let _local7 = lofty::iff::wav::RIFFInfoList::remove(_local7_param0_helper1, _param3);
    let _local8_param0_helper1 = &mut (_local2);
    let _local8_param2_helper1 = _unwrap_option(_local7);
    let _ = lofty::Tag::insert_text(_local8_param0_helper1, _local5, _local8_param2_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 4 {return;}
        let dynamic_length = (data.len() - 0) / 4;
        let _param0 = _to_slice::<u8>(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param1 = _to_slice::<u8>(data, 0 + 1 * dynamic_length, 0 + 2 * dynamic_length);
        let _param2 = _to_str(data, 0 + 2 * dynamic_length, 0 + 3 * dynamic_length);
        let _param3 = _to_str(data, 0 + 3 * dynamic_length, data.len());
        test_function2(_param0 ,_param1 ,_param2 ,_param3);
    });
}
