#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
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

fn test_function43(_param0 :i16 ,_param1 :i16 ,mut _param2 :i32 ,mut _param3 :i32) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i16 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1 = <subtle::Choice as std::ops::Not>::not(_local0);
    let _local2_param0_helper1 = &mut (_param2);
    let _local2_param1_helper1 = &mut (_param3);
    let _ = <i32 as subtle::ConditionallySelectable>::conditional_swap(_local2_param0_helper1, _local2_param1_helper1, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 12 {return;}
        let _param0 = _to_i16(data, 0);
        let _param1 = _to_i16(data, 2);
        let _param2 = _to_i32(data, 4);
        let _param3 = _to_i32(data, 8);
        test_function43(_param0 ,_param1 ,_param2 ,_param3);
    });
}
