#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function146(mut _param0 :html2text::render::text_renderer::TrivialDecorator) {
    let _local0_param0_helper1 = &mut (_param0);
    let _ = <html2text::render::text_renderer::TrivialDecorator as html2text::render::text_renderer::TextDecorator>::decorate_em_end(_local0_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = html2text::render::text_renderer::TrivialDecorator{};
        test_function146(_param0);
    });
}
