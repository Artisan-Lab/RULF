#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

use subtle::ConstantTimeEq; // trait
use std::convert::From; // trait

fn test_function156(_param0 :i16 ,_param1 :i16 ,_param2 :u8) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i16 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1 = <subtle::Choice as std::convert::From::<u8>>::from(_param2);
    let _: subtle::CtOption::<subtle::Choice> = subtle::CtOption::<subtle::Choice>::new(_local0, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 5 {return;}
        let _param0 = _to_i16(data, 0);
        let _param1 = _to_i16(data, 2);
        let _param2 = _to_u8(data, 4);
        test_function156(_param0 ,_param1 ,_param2);
    });
}
