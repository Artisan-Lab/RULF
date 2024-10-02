#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

use subtle::ConditionallySelectable; // trait
use subtle::ConstantTimeEq; // trait

fn test_function49(_param0 :&[u8] ,_param1 :&[u8] ,_param2 :u16 ,_param3 :u16) {
    let _local0: subtle::Choice = <[u8] as subtle::ConstantTimeEq>::ct_eq(_param0, _param1);
    let _local1_param0_helper1 = &(_param2);
    let _local1_param1_helper1 = &(_param3);
    let _ = <u16 as subtle::ConditionallySelectable>::conditional_select(_local1_param0_helper1, _local1_param1_helper1, _local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 6 {return;}
        let dynamic_length = (data.len() - 4) / 2;
        let _param0 = _to_slice::<u8>(data, 4 + 0 * dynamic_length, 4 + 1 * dynamic_length);
        let _param1 = _to_slice::<u8>(data, 4 + 1 * dynamic_length, data.len());
        let _param2 = _to_u16(data, 0);
        let _param3 = _to_u16(data, 2);
        test_function49(_param0 ,_param1 ,_param2 ,_param3);
    });
}
