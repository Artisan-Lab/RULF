#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

use subtle::ConstantTimeEq; // trait

fn test_function179(_param0 :i8 ,_param1 :i8 ,_param2 :u8) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i8 as subtle::ConstantTimeEq>::ct_ne(_local0_param0_helper1, _local0_param1_helper1);
    let _: subtle::CtOption::<u8> = subtle::CtOption::<u8>::new(_param2, _local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 3 {return;}
        let _param0 = _to_i8(data, 0);
        let _param1 = _to_i8(data, 1);
        let _param2 = _to_u8(data, 2);
        test_function179(_param0 ,_param1 ,_param2);
    });
}
