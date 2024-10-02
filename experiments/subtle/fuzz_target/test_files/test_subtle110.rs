#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

use subtle::ConditionallySelectable; // trait
use subtle::ConstantTimeEq; // trait

fn test_function110(_param0 :i8 ,_param1 :i8 ,_param2 :i32 ,_param3 :i8 ,_param4 :i8 ,_param5 :i32 ,_param6 :i8 ,_param7 :i8) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1: subtle::CtOption::<i32> = subtle::CtOption::<i32>::new(_param2, _local0);
    let _local2_param0_helper1 = &(_param3);
    let _local2_param1_helper1 = &(_param4);
    let _local2 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local2_param0_helper1, _local2_param1_helper1);
    let _local3: subtle::CtOption::<i32> = subtle::CtOption::<i32>::new(_param5, _local2);
    let _local4_param0_helper1 = &(_param6);
    let _local4_param1_helper1 = &(_param7);
    let _local4 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local4_param0_helper1, _local4_param1_helper1);
    let _local5_param0_helper1 = &(_local1);
    let _local5_param1_helper1 = &(_local3);
    let _: subtle::CtOption::<i32> = <subtle::CtOption::<i32> as subtle::ConditionallySelectable>::conditional_select(_local5_param0_helper1, _local5_param1_helper1, _local4);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 14 {return;}
        let _param0 = _to_i8(data, 0);
        let _param1 = _to_i8(data, 1);
        let _param2 = _to_i32(data, 2);
        let _param3 = _to_i8(data, 6);
        let _param4 = _to_i8(data, 7);
        let _param5 = _to_i32(data, 8);
        let _param6 = _to_i8(data, 12);
        let _param7 = _to_i8(data, 13);
        test_function110(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5 ,_param6 ,_param7);
    });
}
