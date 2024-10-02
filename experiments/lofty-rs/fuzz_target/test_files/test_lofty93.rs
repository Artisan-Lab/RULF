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

fn test_function93(_param0 :&str) {
    let mut _local0 = lofty::id3::v2::Id3v2Tag::new();
    let _local1_param0_helper1 = &mut (_local0);
    let _local1 = lofty::id3::v2::Id3v2Tag::remove_user_text(_local1_param0_helper1, _param0);
    let _local2_param0_helper1 = _unwrap_option(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _ = lofty::id3::v2::Frame::<'_>::flags(_local2_param0_helper2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        test_function93(_param0);
    });
}
