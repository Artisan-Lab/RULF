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

fn test_function142(_param0 :u16 ,_param1 :u16) {
    let _local0 = tui::backend::TestBackend::new(_param0, _param1);
    let _: std::io::Result::<tui::terminal::Terminal::<tui::backend::TestBackend>> = tui::terminal::Terminal::<tui::backend::TestBackend>::new(_local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_u16(data, 0);
        let _param1 = _to_u16(data, 2);
        test_function142(_param0 ,_param1);
    });
}
