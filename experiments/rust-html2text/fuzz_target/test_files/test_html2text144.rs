#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function144(_param0 :html2text::render::text_renderer::RichDecorator) {
    let _local0_param0_helper1 = &(_param0);
    let _ = <html2text::render::text_renderer::RichDecorator as html2text::render::text_renderer::TextDecorator>::make_subblock_decorator(_local0_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = html2text::render::text_renderer::RichDecorator{};
        test_function144(_param0);
    });
}
