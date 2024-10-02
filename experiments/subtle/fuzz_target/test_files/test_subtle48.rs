#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

use subtle::ConditionallySelectable; // trait
use subtle::ConstantTimeEq; // trait

fn test_function48(_param0 :&[u8] ,_param1 :&[u8] ,mut _param2 :i8 ,mut _param3 :i8) {
    let _local0: subtle::Choice = <[u8] as subtle::ConstantTimeEq>::ct_eq(_param0, _param1);
    let _local1_param0_helper1 = &mut (_param2);
    let _local1_param1_helper1 = &mut (_param3);
    let _ = <i8 as subtle::ConditionallySelectable>::conditional_swap(_local1_param0_helper1, _local1_param1_helper1, _local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 4 {return;}
        let dynamic_length = (data.len() - 2) / 2;
        let _param0 = _to_slice::<u8>(data, 2 + 0 * dynamic_length, 2 + 1 * dynamic_length);
        let _param1 = _to_slice::<u8>(data, 2 + 1 * dynamic_length, data.len());
        let _param2 = _to_i8(data, 0);
        let _param3 = _to_i8(data, 1);
        test_function48(_param0 ,_param1 ,_param2 ,_param3);
    });
}
