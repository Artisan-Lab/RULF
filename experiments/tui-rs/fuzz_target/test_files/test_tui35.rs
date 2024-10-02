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

fn test_function35(_param0 :&str ,_param1 :tui::layout::Rect ,_param2 :u16 ,_param3 :u16 ,_param4 :u16) {
    let _local0 = <tui::text::Spans::<'_> as std::convert::From::<&str>>::from(_param0);
    let mut _local1 = tui::buffer::Buffer::empty(_param1);
    let _local2_param0_helper1 = &mut (_local1);
    let _local2_param3_helper1 = &(_local0);
    let _ = tui::buffer::Buffer::set_spans(_local2_param0_helper1, _param2, _param3, _local2_param3_helper1, _param4);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 15 {return;}
        let dynamic_length = (data.len() - 14) / 1;
        let _param0 = _to_str(data, 14 + 0 * dynamic_length, data.len());
        let _param1 = tui::layout::Rect{x: _to_u16(data, 0), y: _to_u16(data, 2), width: _to_u16(data, 4), height: _to_u16(data, 6)};
        let _param2 = _to_u16(data, 8);
        let _param3 = _to_u16(data, 10);
        let _param4 = _to_u16(data, 12);
        test_function35(_param0 ,_param1 ,_param2 ,_param3 ,_param4);
    });
}
