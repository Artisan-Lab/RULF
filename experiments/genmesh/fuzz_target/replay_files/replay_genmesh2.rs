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

fn test_function2(_param0 :&str ,_param1 :&str ,_param2 :&str ,_param3 :&str ,_param4 :&str ,_param5 :&str ,_param6 :&str ,_param7 :&str) {
    let mut _local0 = <std::string::String as std::convert::From::<&str>>::from(_param0);
    let mut _local1 = <std::string::String as std::convert::From::<&str>>::from(_param1);
    let mut _local2 = <std::string::String as std::convert::From::<&str>>::from(_param2);
    let mut _local3 = <std::string::String as std::convert::From::<&str>>::from(_param3);
    let _local4_param0_helper1 = &mut (_local0);
    let _local4_param1_helper1 = &mut (_local1);
    let _local4_param2_helper1 = &mut (_local2);
    let _local4_param3_helper1 = &mut (_local3);
    let _local4: genmesh::Quad::<&mut std::string::String> = genmesh::Quad::<&mut std::string::String>::new(_local4_param0_helper1, _local4_param1_helper1, _local4_param2_helper1, _local4_param3_helper1);
    let mut _local5 = <std::string::String as std::convert::From::<&str>>::from(_param4);
    let mut _local6 = <std::string::String as std::convert::From::<&str>>::from(_param5);
    let mut _local7 = <std::string::String as std::convert::From::<&str>>::from(_param6);
    let mut _local8 = <std::string::String as std::convert::From::<&str>>::from(_param7);
    let _local9_param0_helper1 = &mut (_local5);
    let _local9_param1_helper1 = &mut (_local6);
    let _local9_param2_helper1 = &mut (_local7);
    let _local9_param3_helper1 = &mut (_local8);
    let _local9: genmesh::Quad::<&mut std::string::String> = genmesh::Quad::<&mut std::string::String>::new(_local9_param0_helper1, _local9_param1_helper1, _local9_param2_helper1, _local9_param3_helper1);
    let _: genmesh::Line::<genmesh::Quad::<&mut std::string::String>> = genmesh::Line::<genmesh::Quad::<&mut std::string::String>>::new(_local4, _local9);
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
    if data.len() < 8 {return;}
    let dynamic_length = (data.len() - 0) / 8;
    let _param0 = _to_str(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
    let _param1 = _to_str(data, 0 + 1 * dynamic_length, 0 + 2 * dynamic_length);
    let _param2 = _to_str(data, 0 + 2 * dynamic_length, 0 + 3 * dynamic_length);
    let _param3 = _to_str(data, 0 + 3 * dynamic_length, 0 + 4 * dynamic_length);
    let _param4 = _to_str(data, 0 + 4 * dynamic_length, 0 + 5 * dynamic_length);
    let _param5 = _to_str(data, 0 + 5 * dynamic_length, 0 + 6 * dynamic_length);
    let _param6 = _to_str(data, 0 + 6 * dynamic_length, 0 + 7 * dynamic_length);
    let _param7 = _to_str(data, 0 + 7 * dynamic_length, data.len());
    test_function2(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5 ,_param6 ,_param7);

}