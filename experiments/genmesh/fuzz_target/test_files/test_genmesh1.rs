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

fn test_function1(_param0 :&str ,_param1 :&str) {
    let _local0 = <std::vec::Vec::<u8, std::alloc::Global> as std::convert::From::<&str>>::from(_param0);
    let _local1 = <std::vec::Vec::<u8, std::alloc::Global> as std::convert::From::<&str>>::from(_param1);
    let _local2: genmesh::Line::<std::vec::Vec::<u8, std::alloc::Global>> = genmesh::Line::<std::vec::Vec::<u8, std::alloc::Global>>::new(_local0, _local1);
    let mut _local3 = std::collections::hash_map::DefaultHasher::new();
    let _local4_param0_helper1 = &(_local2);
    let _local4_param1_helper1 = &mut (_local3);
    let _: () = <genmesh::Line::<std::vec::Vec::<u8, std::alloc::Global>> as std::hash::Hash>::hash(_local4_param0_helper1, _local4_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 0) / 2;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param1 = _to_str(data, 0 + 1 * dynamic_length, data.len());
        test_function1(_param0 ,_param1);
    });
}
