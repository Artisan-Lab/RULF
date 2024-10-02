#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function30(_param0 :i8 ,_param1 :i8 ,_param2 :i8 ,_param3 :i8 ,_param4 :i8 ,_param5 :i8) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let mut _local0 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1_param0_helper1 = &(_param2);
    let _local1_param1_helper1 = &(_param3);
    let mut _local1 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local1_param0_helper1, _local1_param1_helper1);
    let _local2_param0_helper1 = &(_param4);
    let _local2_param1_helper1 = &(_param5);
    let _local2 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local2_param0_helper1, _local2_param1_helper1);
    let _local3_param0_helper1 = &mut (_local0);
    let _local3_param1_helper1 = &mut (_local1);
    let _ = <subtle::Choice as subtle::ConditionallySelectable>::conditional_swap(_local3_param0_helper1, _local3_param1_helper1, _local2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 6 {return;}
        let _param0 = _to_i8(data, 0);
        let _param1 = _to_i8(data, 1);
        let _param2 = _to_i8(data, 2);
        let _param3 = _to_i8(data, 3);
        let _param4 = _to_i8(data, 4);
        let _param5 = _to_i8(data, 5);
        test_function30(_param0 ,_param1 ,_param2 ,_param3 ,_param4 ,_param5);
    });
}
