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

fn _to_u64(data:&[u8], index:usize)->u64 {
    let data0 = _to_u32(data, index) as u64;
    let data1 = _to_u32(data, index+4) as u64;
    data0 << 32 | data1
}

fn _to_usize(data:&[u8], index:usize)->usize {
    _to_u64(data, index) as usize
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect("slice with incorrect length");
    f32::from_le_bytes(data_array)
}

fn test_function9(_param0 :&str ,_param1 :f32 ,_param2 :usize ,_param3 :fontdue::layout::GlyphRasterConfig) {
    let _: fontdue::layout::TextStyle::<'_, fontdue::layout::GlyphRasterConfig> = fontdue::layout::TextStyle::<'_, fontdue::layout::GlyphRasterConfig>::with_user_data(_param0, _param1, _param2, _param3);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 27 {return;}
        let dynamic_length = (data.len() - 26) / 1;
        let _param0 = _to_str(data, 26 + 0 * dynamic_length, data.len());
        let _param1 = _to_f32(data, 0);
        let _param2 = _to_usize(data, 4);
        let _param3 = fontdue::layout::GlyphRasterConfig{glyph_index: _to_u16(data, 12), px: _to_f32(data, 14), font_hash: _to_usize(data, 18)};
        test_function9(_param0 ,_param1 ,_param2 ,_param3);
    });
}
