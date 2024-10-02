#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

use std::convert::From; // trait

fn test_function299(_param0 :u8 ,_param1 :u8) {
    let _local0 = <subtle::Choice as std::convert::From::<u8>>::from(_param0);
    let _: subtle::CtOption::<u8> = subtle::CtOption::<u8>::new(_param1, _local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_u8(data, 1);
        test_function299(_param0 ,_param1);
    });
}
