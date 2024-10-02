#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
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

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i128(data:&[u8], index:usize)->i128 {
    let data0 = _to_i64(data, index) as i128;
    let data1 = _to_i64(data, index+8) as i128;
    data0 << 64 | data1
}

use subtle::ConstantTimeEq; // trait

fn test_function120(_param0 :i8 ,_param1 :i8 ,_param2 :i128 ,_param3 :i8 ,_param4 :i8 ,_param5 :i128) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1: subtle::CtOption::<i128> = subtle::CtOption::<i128>::new(_param2, _local0);
    let _local2_param0_helper1 = &(_param3);
    let _local2_param1_helper1 = &(_param4);
    let _local2 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local2_param0_helper1, _local2_param1_helper1);
    let _local3: subtle::CtOption::<i128> = subtle::CtOption::<i128>::new(_param5, _local2);
    let _local4_param0_helper1 = &(_local1);
    let _local4_param1_helper1 = &(_local3);
    let _: subtle::Choice = <subtle::CtOption::<i128> as subtle::ConstantTimeEq>::ct_eq(_local4_param0_helper1, _local4_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 36 {return;}
        let _param0 = _to_i8(data, 0);
        let _param1 = _to_i8(data, 1);
        let _param2 = _to_i128(data, 2);
        let _param3 = _to_i8(data, 18);
        let _param4 = _to_i8(data, 19);
        let _param5 = _to_i128(data, 20);
        test_function120(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5);
    });
}
