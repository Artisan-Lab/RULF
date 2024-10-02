#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
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

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn test_function141(_param0 :&str ,_param1 :u32 ,_param2 :bool) {
    let _local0 = <std::vec::Vec::<u8, std::alloc::Global> as std::convert::From::<&str>>::from(_param0);
    let _local1: flate2::CrcWriter::<std::vec::Vec::<u8, std::alloc::Global>> = flate2::CrcWriter::<std::vec::Vec::<u8, std::alloc::Global>>::new(_local0);
    let _local2 = flate2::Compression::new(_param1);
    let _local3 = flate2::Compress::new(_local2, _param2);
    let _local4: flate2::write::ZlibEncoder::<flate2::CrcWriter::<std::vec::Vec::<u8, std::alloc::Global>>> = flate2::write::ZlibEncoder::<flate2::CrcWriter::<std::vec::Vec::<u8, std::alloc::Global>>>::new_with_compress(_local1, _local3);
    let _: std::io::Result::<flate2::CrcWriter::<std::vec::Vec::<u8, std::alloc::Global>>> = flate2::write::ZlibEncoder::<flate2::CrcWriter::<std::vec::Vec::<u8, std::alloc::Global>>>::flush_finish(_local4);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 6 {return;}
        let dynamic_length = (data.len() - 5) / 1;
        let _param0 = _to_str(data, 5 + 0 * dynamic_length, data.len());
        let _param1 = _to_u32(data, 0);
        let _param2 = _to_bool(data, 4);
        test_function141(_param0 ,_param1 ,_param2);
    });
}
