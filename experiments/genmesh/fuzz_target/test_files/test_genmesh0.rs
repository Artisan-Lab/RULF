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

fn test_function0(_param0 :&str ,_param1 :&str ,_param2 :&str ,_param3 :&str) {
    let _local0 = <std::string::String as std::convert::From::<&str>>::from(_param0);
    let _local1 = <std::string::String as std::convert::From::<&str>>::from(_param1);
    let _local2: genmesh::Line::<std::string::String> = genmesh::Line::<std::string::String>::new(_local0, _local1);
    let _local3 = <std::string::String as std::convert::From::<&str>>::from(_param2);
    let _local4 = <std::string::String as std::convert::From::<&str>>::from(_param3);
    let _local5: genmesh::Line::<std::string::String> = genmesh::Line::<std::string::String>::new(_local3, _local4);
    let _local6: genmesh::Line::<genmesh::Line::<std::string::String>> = genmesh::Line::<genmesh::Line::<std::string::String>>::new(_local2, _local5);
    let mut _local7 = std::collections::hash_map::DefaultHasher::new();
    let _local8_param0_helper1 = &(_local6);
    let _local8_param1_helper1 = &mut (_local7);
    let _: () = <genmesh::Line::<genmesh::Line::<std::string::String>> as std::hash::Hash>::hash(_local8_param0_helper1, _local8_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 4 {return;}
        let dynamic_length = (data.len() - 0) / 4;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param1 = _to_str(data, 0 + 1 * dynamic_length, 0 + 2 * dynamic_length);
        let _param2 = _to_str(data, 0 + 2 * dynamic_length, 0 + 3 * dynamic_length);
        let _param3 = _to_str(data, 0 + 3 * dynamic_length, data.len());
        test_function0(_param0 ,_param1 ,_param2 ,_param3);
    });
}
