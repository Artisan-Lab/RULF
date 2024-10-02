#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function0(_param0 :i8 ,_param1 :i8 ,_param2 :i8 ,_param3 :i8) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <i8 as subtle::ConstantTimeEq>::ct_eq(_local0_param0_helper1, _local0_param1_helper1);
    let _local1_param0_helper1 = &(_param2);
    let _local1_param1_helper1 = &(_param3);
    let _local1 = <i8 as subtle::ConstantTimeEq>::ct_ne(_local1_param0_helper1, _local1_param1_helper1);
    let _ = <subtle::Choice as std::ops::BitAnd::<subtle::Choice>>::bitand(_local0, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_i8(data, 0);
        let _param1 = _to_i8(data, 1);
        let _param2 = _to_i8(data, 2);
        let _param3 = _to_i8(data, 3);
        test_function0(_param0 ,_param1 ,_param2 ,_param3);
    });
}
