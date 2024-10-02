#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn test_function159(_param0 :bool ,_param1 :bool) {
    let mut _local0 = flate2::Decompress::new(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let _ = flate2::Decompress::reset(_local1_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_bool(data, 0);
        let _param1 = _to_bool(data, 1);
        test_function159(_param0 ,_param1);
    });
}
