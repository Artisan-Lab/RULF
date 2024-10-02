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

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function21(_param0 :usize ,_param1 :html2text::render::text_renderer::RichDecorator ,_param2 :&[char]) {
    let mut _local0: html2text::render::text_renderer::SubRenderer::<html2text::render::text_renderer::RichDecorator> = html2text::render::text_renderer::SubRenderer::<html2text::render::text_renderer::RichDecorator>::new(_param0, _param1);
    let _local1_param0_helper1 = &mut (_local0);
    let _ = <html2text::render::text_renderer::SubRenderer::<html2text::render::text_renderer::RichDecorator> as html2text::render::Renderer>::append_vert_row(_local1_param0_helper1, _param2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 12 {return;}
        let dynamic_length = (data.len() - 8) / 1;
        let _param0 = _to_usize(data, 0);
        let _param1 = html2text::render::text_renderer::RichDecorator{};
        let _param2 = _to_slice::<char>(data, 8 + 0 * dynamic_length, data.len());
        test_function21(_param0 ,_param1 ,_param2);
    });
}
