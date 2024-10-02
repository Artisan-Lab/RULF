#[macro_use]
extern crate afl;
extern crate subtle;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

use subtle::ConstantTimeEq; // trait

fn test_function200(_param0 :u16 ,_param1 :u16 ,_param2 :u32) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <u16 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1_param0_helper1 = &(_param2) as *const u32;
    let _: subtle::CtOption::<*const u32> = subtle::CtOption::<*const u32>::new(_local1_param0_helper1, _local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 8 {return;}
        let _param0 = _to_u16(data, 0);
        let _param1 = _to_u16(data, 2);
        let _param2 = _to_u32(data, 4);
        test_function200(_param0 ,_param1 ,_param2);
    });
}
