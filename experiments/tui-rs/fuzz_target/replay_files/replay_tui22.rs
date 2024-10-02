#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function22(_param0 :&[(f64 ,f64)] ,_param1 :&[(f64 ,f64)]) {
    let _local0 = <tui::widgets::Dataset::<'_> as std::default::Default>::default();
    let _local1 = tui::widgets::Dataset::<'_>::data(_local0, _param0);
    let _ = tui::widgets::Dataset::<'_>::data(_local1, _param1);
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
    if data.len() < 32 {return;}
    let dynamic_length = (data.len() - 0) / 2;
    let _param0 = _to_slice::<(f64 ,f64)>(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
    let _param1 = _to_slice::<(f64 ,f64)>(data, 0 + 1 * dynamic_length, data.len());
    test_function22(_param0 ,_param1);

}