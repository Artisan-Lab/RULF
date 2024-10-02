#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function8(_param0 :i8 ,_param1 :i8) {
    let _: i8 = num::abs_sub(_param0, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_i8(data, 0);
        let _param1 = _to_i8(data, 1);
        test_function8(_param0 ,_param1);
    });
}
