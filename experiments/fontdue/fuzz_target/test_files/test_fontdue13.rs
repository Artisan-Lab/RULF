#![feature(assoc_char_funcs)]
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

fn test_function13(_param0 :char ,_param1 :u16 ,_param2 :char ,_param3 :u16) {
    let _local0 = fontdue::layout::CharacterData::classify(_param0, _param1);
    let _local1 = fontdue::layout::CharacterData::classify(_param2, _param3);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _ = <fontdue::layout::CharacterData as std::cmp::PartialEq::<fontdue::layout::CharacterData>>::eq(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 12 {return;}
        let _param0 = _to_char(data, 0);
        let _param1 = _to_u16(data, 4);
        let _param2 = _to_char(data, 6);
        let _param3 = _to_u16(data, 10);
        test_function13(_param0 ,_param1 ,_param2 ,_param3);
    });
}
