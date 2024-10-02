#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

use subtle::ConstantTimeEq; // trait
use std::convert::From; // trait

fn test_function66(_param0 :&[u8] ,_param1 :&[u8]) {
    let _local0: subtle::Choice = <[u8] as subtle::ConstantTimeEq>::ct_eq(_param0, _param1);
    let _ = <bool as std::convert::From::<subtle::Choice>>::from(_local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 2 {return;}
        let dynamic_length = (data.len() - 0) / 2;
        let _param0 = _to_slice::<u8>(data, 0 + 0 * dynamic_length, 0 + 1 * dynamic_length);
        let _param1 = _to_slice::<u8>(data, 0 + 1 * dynamic_length, data.len());
        test_function66(_param0 ,_param1);
    });
}
