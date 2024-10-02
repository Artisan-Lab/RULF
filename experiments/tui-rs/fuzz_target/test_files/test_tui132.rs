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

fn test_function132(_param0 :tui::layout::Rect ,_param1 :tui::widgets::Clear ,_param2 :tui::layout::Rect) {
    let mut _local0 = tui::buffer::Buffer::empty(_param0);
    let _local1_param2_helper1 = &mut (_local0);
    let _ = <tui::widgets::Clear as tui::widgets::Widget>::render(_param1, _param2, _local1_param2_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 16 {return;}
        let _param0 = tui::layout::Rect{x: _to_u16(data, 0), y: _to_u16(data, 2), width: _to_u16(data, 4), height: _to_u16(data, 6)};
        let _param1 = tui::widgets::Clear{};
        let _param2 = tui::layout::Rect{x: _to_u16(data, 8), y: _to_u16(data, 10), width: _to_u16(data, 12), height: _to_u16(data, 14)};
        test_function132(_param0 ,_param1 ,_param2);
    });
}
