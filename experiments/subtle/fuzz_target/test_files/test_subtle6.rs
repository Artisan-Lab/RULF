#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function6(_param0 :u8 ,_param1 :i8 ,_param2 :i8) {
    let _local0 = <subtle::Choice as std::convert::From::<u8>>::from(_param0);
    let _local1 = <subtle::Choice as std::ops::Not>::not(_local0);
    let _local2_param0_helper1 = &(_param1);
    let _local2_param1_helper1 = &(_param2);
    let _ = <i8 as subtle::ConditionallySelectable>::conditional_select(_local2_param0_helper1, _local2_param1_helper1, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 3 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_i8(data, 1);
        let _param2 = _to_i8(data, 2);
        test_function6(_param0 ,_param1 ,_param2);
    });
}
