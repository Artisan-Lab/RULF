#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
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
use std::ops::BitAndAssign; // trait

fn test_function44(_param0 :&[u8] ,_param1 :&[u8] ,_param2 :i32 ,_param3 :i32) {
    let mut _local0: subtle::Choice = <[u8] as subtle::ConstantTimeEq>::ct_ne(_param0, _param1);
    let _local1_param0_helper1 = &(_param2);
    let _local1_param1_helper1 = &(_param3);
    let _local1 = <i32 as subtle::ConstantTimeEq>::ct_ne(_local1_param0_helper1, _local1_param1_helper1);
    let _local2_param0_helper1 = &mut (_local0);
    let _ = <subtle::Choice as std::ops::BitAndAssign::<subtle::Choice>>::bitand_assign(_local2_param0_helper1, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 10 {return;}
        let dynamic_length = (data.len() - 8) / 2;
        let _param0 = _to_slice::<u8>(data, 8 + 0 * dynamic_length, 8 + 1 * dynamic_length);
        let _param1 = _to_slice::<u8>(data, 8 + 1 * dynamic_length, data.len());
        let _param2 = _to_i32(data, 0);
        let _param3 = _to_i32(data, 4);
        test_function44(_param0 ,_param1 ,_param2 ,_param3);
    });
}
