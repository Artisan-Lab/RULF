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

fn test_function43(_param0 :&str) {
    let mut _local0 = <lofty::aac::AacFile as std::default::Default>::default();
    let _local1 = <lofty::id3::v2::Id3v2Tag as std::default::Default>::default();
    let _local2_param0_helper1 = &mut (_local0);
    let mut _local2 = lofty::aac::AacFile::set_id3v2(_local2_param0_helper1, _local1);
    let mut _local3 = lofty::iff::wav::RIFFInfoList::new();
    let _local4_param0_helper1 = &mut (_local3);
    let _local4 = lofty::iff::wav::RIFFInfoList::remove(_local4_param0_helper1, _param0);
    let mut _local5_param0_helper1 = _unwrap_option(_local2);
    let _local5_param0_helper2 = &mut (_local5_param0_helper1);
    let _local5_param1_helper1 = _unwrap_option(_local4);
    let _ = <lofty::id3::v2::Id3v2Tag as lofty::Accessor>::set_artist(_local5_param0_helper2, _local5_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        test_function43(_param0);
    });
}
