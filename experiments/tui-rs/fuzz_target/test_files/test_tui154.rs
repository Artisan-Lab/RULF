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

fn test_function154(_param0 :tui::layout::Margin ,_param1 :tui::layout::Margin) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <tui::layout::Margin as std::cmp::PartialEq::<tui::layout::Margin>>::eq(_local0_param0_helper1, _local0_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 8 {return;}
        let _param0 = tui::layout::Margin{vertical: _to_u16(data, 0), horizontal: _to_u16(data, 2)};
        let _param1 = tui::layout::Margin{vertical: _to_u16(data, 4), horizontal: _to_u16(data, 6)};
        test_function154(_param0 ,_param1);
    });
}
