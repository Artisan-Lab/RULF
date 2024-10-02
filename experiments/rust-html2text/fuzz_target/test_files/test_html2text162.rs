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

fn test_function162(_param0 :usize ,_param1 :html2text::render::text_renderer::RichDecorator ,_param2 :usize ,_param3 :usize) {
    let _local0: html2text::render::text_renderer::SubRenderer::<html2text::render::text_renderer::RichDecorator> = html2text::render::text_renderer::SubRenderer::<html2text::render::text_renderer::RichDecorator>::new(_param0, _param1);
    let _local1_param0_helper1 = &(_local0);
    let mut _local1: html2text::render::text_renderer::SubRenderer::<html2text::render::text_renderer::RichDecorator> = <html2text::render::text_renderer::SubRenderer::<html2text::render::text_renderer::RichDecorator> as html2text::render::Renderer>::new_sub_renderer(_local1_param0_helper1, _param2);
    let _local2_param0_helper1 = &mut (_local1);
    let _ = <html2text::render::text_renderer::SubRenderer::<html2text::render::text_renderer::RichDecorator> as html2text::render::Renderer>::add_horizontal_border_width(_local2_param0_helper1, _param3);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 24 {return;}
        let _param0 = _to_usize(data, 0);
        let _param1 = html2text::render::text_renderer::RichDecorator{};
        let _param2 = _to_usize(data, 8);
        let _param3 = _to_usize(data, 16);
        test_function162(_param0 ,_param1 ,_param2 ,_param3);
    });
}
