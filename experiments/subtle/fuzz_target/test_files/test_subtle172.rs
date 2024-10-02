#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

use subtle::ConstantTimeEq; // trait
use subtle::ConstantTimeGreater; // trait

fn test_function172(_param0 :u8 ,_param1 :u8 ,_param2 :u8 ,_param3 :u8) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <u8 as subtle::ConstantTimeGreater>::ct_gt(_local0_param0_helper1, _local0_param1_helper1);
    let _local1_param0_helper1 = &(_param2);
    let _local1_param1_helper1 = &(_param3);
    let _local1 = <u8 as subtle::ConstantTimeEq>::ct_eq(_local1_param0_helper1, _local1_param1_helper1);
    let _: subtle::CtOption::<subtle::Choice> = subtle::CtOption::<subtle::Choice>::new(_local0, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_u8(data, 1);
        let _param2 = _to_u8(data, 2);
        let _param3 = _to_u8(data, 3);
        test_function172(_param0 ,_param1 ,_param2 ,_param3);
    });
}
