#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function91(mut _param0 :()) {
    let _local0_param0_helper1 = &mut (_param0);
    let _ = <() as prost::Message>::clear(_local0_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = ();
        test_function91(_param0);
    });
}
