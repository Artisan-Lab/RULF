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

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

use subtle::ConstantTimeEq; // trait

fn test_function81(_param0 :&[u8] ,_param1 :&[u8] ,_param2 :u32) {
    let _local0: subtle::Choice = <[u8] as subtle::ConstantTimeEq>::ct_eq(_param0, _param1);
    let _local1_param0_helper1 = &(_param2) as *const u32;
    let _local1: subtle::CtOption::<*const u32> = subtle::CtOption::<*const u32>::new(_local1_param0_helper1, _local0);
    let _local2_param0_helper1 = &(_local1);
    let _: subtle::Choice = subtle::CtOption::<*const u32>::is_some(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 6 {return;}
        let dynamic_length = (data.len() - 4) / 2;
        let _param0 = _to_slice::<u8>(data, 4 + 0 * dynamic_length, 4 + 1 * dynamic_length);
        let _param1 = _to_slice::<u8>(data, 4 + 1 * dynamic_length, data.len());
        let _param2 = _to_u32(data, 0);
        test_function81(_param0 ,_param1 ,_param2);
    });
}
