#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

use subtle::ConstantTimeEq; // trait

fn test_function118(_param0 :i8 ,_param1 :i8 ,_param2 :u16 ,_param3 :i8 ,_param4 :i8 ,_param5 :u16) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1: subtle::CtOption::<u16> = subtle::CtOption::<u16>::new(_param2, _local0);
    let _local2_param0_helper1 = &(_param3);
    let _local2_param1_helper1 = &(_param4);
    let _local2 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local2_param0_helper1, _local2_param1_helper1);
    let _local3: subtle::CtOption::<u16> = subtle::CtOption::<u16>::new(_param5, _local2);
    let _local4_param0_helper1 = &(_local1);
    let _local4_param1_helper1 = &(_local3);
    let _: subtle::Choice = <subtle::CtOption::<u16> as subtle::ConstantTimeEq>::ct_ne(_local4_param0_helper1, _local4_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 8 {return;}
        let _param0 = _to_i8(data, 0);
        let _param1 = _to_i8(data, 1);
        let _param2 = _to_u16(data, 2);
        let _param3 = _to_i8(data, 4);
        let _param4 = _to_i8(data, 5);
        let _param5 = _to_u16(data, 6);
        test_function118(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5);
    });
}
