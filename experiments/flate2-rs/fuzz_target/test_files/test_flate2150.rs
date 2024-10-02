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

fn test_function150(_param0 :bool) {
    let _local0 = flate2::Compression::none();
    let _local1 = flate2::Compress::new(_local0, _param0);
    let _local2_param0_helper1 = &(_local1);
    let _ = flate2::Compress::total_in(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_bool(data, 0);
        test_function150(_param0);
    });
}
