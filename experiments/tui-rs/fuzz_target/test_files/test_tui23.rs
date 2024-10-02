#![feature(assoc_char_funcs)]
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

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_char(data:&[u8], index: usize)->char {
    let char_value = _to_u32(data,index);
    match char::from_u32(char_value) {
        Some(c)=>c,
        None=>{
            use std::process;
            process::exit(0);
        }
    }
}

fn test_function23(_param0 :&str ,_param1 :char) {
    let mut _local0 = <tui::buffer::Cell as std::default::Default>::default();
    let _local1_param0_helper1 = &mut (_local0);
    let _local1 = tui::buffer::Cell::set_symbol(_local1_param0_helper1, _param0);
    let _ = tui::buffer::Cell::set_char(_local1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 5 {return;}
        let dynamic_length = (data.len() - 4) / 1;
        let _param0 = _to_str(data, 4 + 0 * dynamic_length, data.len());
        let _param1 = _to_char(data, 0);
        test_function23(_param0 ,_param1);
    });
}
