#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _unwrap_result<T, E>(_res: Result<T, E>) -> T {
    match _res {
        Ok(_t) => _t,
        Err(_) => {
            use std::process;
            process::exit(0);
        },
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

fn test_function7(_param0 :&str ,_param1 :&[u8]) {
    let _local0 = base64::engine::general_purpose::GeneralPurposeConfig::new();
    let _local1 = base64::alphabet::Alphabet::new(_param0);
    let _local2_param0_helper1 = _unwrap_result(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2 = base64::engine::general_purpose::GeneralPurpose::new(_local2_param0_helper2, _local0);
    let _local3_param0_helper1 = &(_local2);
    let mut _local3: base64::write::EncoderStringWriter::<'_, base64::engine::general_purpose::GeneralPurpose, std::string::String> = base64::write::EncoderStringWriter::<'_, base64::engine::general_purpose::GeneralPurpose, std::string::String>::new(_local3_param0_helper1);
    let _local4_param0_helper1 = &mut (_local3);
    let _: std::io::Result::<usize> = <base64::write::EncoderStringWriter::<'_, base64::engine::general_purpose::GeneralPurpose, std::string::String> as std::io::Write>::write(_local4_param0_helper1, _param1);
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
    if data.len() < 2 {return;}
    let dynamic_length = (data.len() - 0) / 2;
    let _param0 = _to_str(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
    let _param1 = _to_slice::<u8>(data, 0 + 1 * dynamic_length, data.len());
    test_function7(_param0 ,_param1);

}