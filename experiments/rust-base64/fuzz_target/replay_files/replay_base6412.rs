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

fn test_function12(_param0 :&str ,_param1 :&str) {
    let _local0 = base64::engine::general_purpose::GeneralPurposeConfig::new();
    let _local1 = base64::alphabet::Alphabet::new(_param0);
    let _local2_param0_helper1 = _unwrap_result(_local1);
    let _local2_param0_helper2 = &(_local2_param0_helper1);
    let _local2 = base64::engine::general_purpose::GeneralPurpose::new(_local2_param0_helper2, _local0);
    let _local3_param0_helper1 = &(_local2);
    let _local3: base64::write::EncoderStringWriter::<'_, base64::engine::general_purpose::GeneralPurpose, std::string::String> = base64::write::EncoderStringWriter::<'_, base64::engine::general_purpose::GeneralPurpose, std::string::String>::new(_local3_param0_helper1);
    let _local4 = base64::engine::general_purpose::GeneralPurposeConfig::new();
    let _local5 = base64::alphabet::Alphabet::new(_param1);
    let _local6_param0_helper1 = _unwrap_result(_local5);
    let _local6_param0_helper2 = &(_local6_param0_helper1);
    let _local6 = base64::engine::general_purpose::GeneralPurpose::new(_local6_param0_helper2, _local4);
    let _local7_param1_helper1 = &(_local6);
    let mut _local7: base64::write::EncoderWriter::<'_, base64::engine::general_purpose::GeneralPurpose, base64::write::EncoderStringWriter::<'_, base64::engine::general_purpose::GeneralPurpose, std::string::String>> = base64::write::EncoderWriter::<'_, base64::engine::general_purpose::GeneralPurpose, base64::write::EncoderStringWriter::<'_, base64::engine::general_purpose::GeneralPurpose, std::string::String>>::new(_local3, _local7_param1_helper1);
    let _local8_param0_helper1 = &mut (_local7);
    let _: std::io::Result::<()> = <base64::write::EncoderWriter::<'_, base64::engine::general_purpose::GeneralPurpose, base64::write::EncoderStringWriter::<'_, base64::engine::general_purpose::GeneralPurpose, std::string::String>> as std::io::Write>::flush(_local8_param0_helper1);
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
    let _param1 = _to_str(data, 0 + 1 * dynamic_length, data.len());
    test_function12(_param0 ,_param1);

}