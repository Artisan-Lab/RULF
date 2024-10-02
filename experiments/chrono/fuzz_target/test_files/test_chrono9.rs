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

fn test_function9(_param0 :chrono::offset::Utc ,_param1 :&str ,_param2 :&str) {
    let _local0_param0_helper1 = &(_param0);
    let _local0 = <chrono::offset::Utc as chrono::offset::Offset>::fix(_local0_param0_helper1);
    let _local1_param0_helper1 = &(_local0);
    let _local1 = <chrono::offset::FixedOffset as chrono::offset::TimeZone>::from_offset(_local1_param0_helper1);
    let _local2_param0_helper1 = &(_local1);
    let _ = <chrono::offset::FixedOffset as chrono::offset::TimeZone>::datetime_from_str(_local2_param0_helper1, _param1, _param2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 0) / 2;
        let _param0 = chrono::offset::Utc{};
        let _param1 = _to_str(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param2 = _to_str(data, 0 + 1 * dynamic_length, data.len());
        test_function9(_param0 ,_param1 ,_param2);
    });
}
