#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function62(_param0 :tui::layout::Rect ,_param1 :u16 ,_param2 :u16 ,_param3 :tui::layout::Rect) {
    let _local0 = tui::buffer::Buffer::empty(_param0);
    let _local1_param0_helper1 = &(_local0);
    let _local1 = tui::buffer::Buffer::get(_local1_param0_helper1, _param1, _param2);
    let _ = tui::buffer::Buffer::filled(_param3, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 20 {return;}
        let _param0 = tui::layout::Rect{x: _to_u16(data, 0), y: _to_u16(data, 2), width: _to_u16(data, 4), height: _to_u16(data, 6)};
        let _param1 = _to_u16(data, 8);
        let _param2 = _to_u16(data, 10);
        let _param3 = tui::layout::Rect{x: _to_u16(data, 12), y: _to_u16(data, 14), width: _to_u16(data, 16), height: _to_u16(data, 18)};
        test_function62(_param0 ,_param1 ,_param2 ,_param3);
    });
}
