#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
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

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function10(_param0 :u32 ,_param1 :u32 ,mut _param2 :i8 ,mut _param3 :i8) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <u32 as subtle::ConstantTimeLess>::ct_lt(_local0_param0_helper1, _local0_param1_helper1);
    let _local1 = <subtle::Choice as std::ops::Not>::not(_local0);
    let _local2_param0_helper1 = &mut (_param2);
    let _local2_param1_helper1 = &mut (_param3);
    let _ = <i8 as subtle::ConditionallySelectable>::conditional_swap(_local2_param0_helper1, _local2_param1_helper1, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 10 {return;}
        let _param0 = _to_u32(data, 0);
        let _param1 = _to_u32(data, 4);
        let _param2 = _to_i8(data, 8);
        let _param3 = _to_i8(data, 9);
        test_function10(_param0 ,_param1 ,_param2 ,_param3);
    });
}
