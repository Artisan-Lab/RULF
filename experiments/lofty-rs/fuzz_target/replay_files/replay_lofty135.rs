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

fn test_function135(_param0 :usize ,_param1 :lofty::PictureInformation) {
    let _local0 = <lofty::id3::v1::Id3v1Tag as std::default::Default>::default();
    let _local1 = <lofty::Tag as std::convert::From::<lofty::id3::v1::Id3v1Tag>>::from(_local0);
    let mut _local2 = <lofty::ogg::VorbisComments as std::convert::From::<lofty::Tag>>::from(_local1);
    let _local3 = lofty::iff::aiff::AIFFTextChunks::new();
    let mut _local4 = <lofty::Tag as std::convert::From::<lofty::iff::aiff::AIFFTextChunks>>::from(_local3);
    let _local5_param0_helper1 = &mut (_local4);
    let _local5 = lofty::Tag::remove_picture(_local5_param0_helper1, _param0);
    let _local6_param0_helper1 = &mut (_local2);
    let _local6_param2_helper1 = Some(_param1);
    let _ = <lofty::ogg::VorbisComments as lofty::ogg::OggPictureStorage>::insert_picture(_local6_param0_helper1, _local5, _local6_param2_helper1);
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
    if data.len() != 24 {return;}
    let _param0 = _to_usize(data, 0);
    let _param1 = lofty::PictureInformation{width: _to_u32(data, 8), height: _to_u32(data, 12), color_depth: _to_u32(data, 16), num_colors: _to_u32(data, 20)};
    test_function135(_param0 ,_param1);

}