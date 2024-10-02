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

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn test_function10(_param0 :u32 ,_param1 :&str) {
    let _local0 = <xorfilter::BuildHasherDefault as std::default::Default>::default();
    let _local1: xorfilter::Fuse8::<xorfilter::BuildHasherDefault> = xorfilter::Fuse8::<xorfilter::BuildHasherDefault>::with_hasher(_param0, _local0);
    let _local2 = <std::vec::Vec::<u8, std::alloc::Global> as std::convert::From::<&str>>::from(_param1);
    let _local3_param0_helper1 = &(_local1);
    let _local3_param1_helper1 = &(_local2);
    let _: bool = xorfilter::Fuse8::<xorfilter::BuildHasherDefault>::contains(_local3_param0_helper1, _local3_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 5 {return;}
        let dynamic_length = (data.len() - 4) / 1;
        let _param0 = _to_u32(data, 0);
        let _param1 = _to_str(data, 4 + 0 * dynamic_length, data.len());
        test_function10(_param0 ,_param1);
    });
}
