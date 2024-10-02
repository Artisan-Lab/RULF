#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
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

fn test_function0(_param0 :u8 ,_param1 :&str ,_param2 :&str ,_param3 :usize) {
    let _local0 = lofty::PictureType::from_u8(_param0);
    let _local1 = lofty::MimeType::from_str(_param1);
    let mut _local2 = lofty::iff::wav::RIFFInfoList::new();
    let _local3_param0_helper1 = &mut (_local2);
    let _local3 = lofty::iff::wav::RIFFInfoList::remove(_local3_param0_helper1, _param2);
    let _local4 = lofty::iff::aiff::AIFFTextChunks::new();
    let mut _local5 = <lofty::Tag as std::convert::From::<lofty::iff::aiff::AIFFTextChunks>>::from(_local4);
    let _local6_param0_helper1 = &mut (_local5);
    let _local6 = lofty::Tag::remove_picture(_local6_param0_helper1, _param3);
    let _local7_param0_helper1 = &(_local6);
    let _local7 = lofty::Picture::as_ape_bytes(_local7_param0_helper1);
    let _ = lofty::Picture::new_unchecked(_local0, _local1, _local3, _local7);
}

fn _read_data()-> Vec<u8> {
    use std::env;
    use std::process::exit;
    let args:Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("No crash filename provided");
        exit(-1);
    }
    use std::path::PathBuf;
    let crash_file_name = &args[1];
    let crash_path = PathBuf::from(crash_file_name);
    if !crash_path.is_file() {
        println!("Not a valid crash file");
        exit(-1);
    }
    use std::fs;
    let data =  fs::read(crash_path).unwrap();
    data
}

fn main() {
    let _content = _read_data();
    let data = &_content;
    println!("data = {:?}", data);
    println!("data len = {:?}", data.len());
    //actual body emit
    if data.len() < 11 {return;}
    let dynamic_length = (data.len() - 9) / 2;
    let _param0 = _to_u8(data, 0);
    let _param1 = _to_str(data, 9 + 0 * dynamic_length, 9 + 1 * dynamic_length);
    let _param2 = _to_str(data, 9 + 1 * dynamic_length, data.len());
    let _param3 = _to_usize(data, 1);
    test_function0(_param0 ,_param1 ,_param2 ,_param3);

}