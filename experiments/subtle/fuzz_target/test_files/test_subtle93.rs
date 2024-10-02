#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
}

fn _to_isize(data:&[u8], index:usize)->isize {
    _to_i64(data, index) as isize
}

fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
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

fn test_function93(_param0 :i8 ,_param1 :i8 ,_param2 :isize ,_param3 :i8 ,_param4 :i8 ,_param5 :isize) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1: subtle::CtOption::<isize> = subtle::CtOption::<isize>::new(_param2, _local0);
    let _local2_param0_helper1 = &(_param3);
    let _local2_param1_helper1 = &(_param4);
    let _local2 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local2_param0_helper1, _local2_param1_helper1);
    let _local3: subtle::CtOption::<isize> = subtle::CtOption::<isize>::new(_param5, _local2);
    let _local4_param0_helper1 = &(_local1);
    let _local4_param1_helper1 = &(_local3);
    let _: subtle::Choice = <subtle::CtOption::<isize> as subtle::ConstantTimeEq>::ct_ne(_local4_param0_helper1, _local4_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 20 {return;}
        let _param0 = _to_i8(data, 0);
        let _param1 = _to_i8(data, 1);
        let _param2 = _to_isize(data, 2);
        let _param3 = _to_i8(data, 10);
        let _param4 = _to_i8(data, 11);
        let _param5 = _to_isize(data, 12);
        test_function93(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5);
    });
}
