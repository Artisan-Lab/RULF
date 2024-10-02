#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_isize(data:&[u8], index:usize)->isize {
    _to_i64(data, index) as isize
}

fn _to_u128(data:&[u8], index:usize)->u128 {
    let data0 = _to_u64(data, index) as u128;
    let data1 = _to_u64(data, index+8) as u128;
    data0 << 64 | data1
}

fn _to_u64(data:&[u8], index:usize)->u64 {
    let data0 = _to_u32(data, index) as u64;
    let data1 = _to_u32(data, index+4) as u64;
    data0 << 32 | data1
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

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

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

use subtle::ConstantTimeEq; // trait

fn test_function274(_param0 :u128 ,_param1 :u128 ,_param2 :isize) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <u128 as subtle::ConstantTimeEq>::ct_ne(_local0_param0_helper1, _local0_param1_helper1);
    let _: subtle::CtOption::<isize> = subtle::CtOption::<isize>::new(_param2, _local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 40 {return;}
        let _param0 = _to_u128(data, 0);
        let _param1 = _to_u128(data, 16);
        let _param2 = _to_isize(data, 32);
        test_function274(_param0 ,_param1 ,_param2);
    });
}
