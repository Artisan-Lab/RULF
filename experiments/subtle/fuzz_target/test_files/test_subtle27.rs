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

fn _to_u64(data:&[u8], index:usize)->u64 {
    let data0 = _to_u32(data, index) as u64;
    let data1 = _to_u32(data, index+4) as u64;
    data0 << 32 | data1
}

fn _to_usize(data:&[u8], index:usize)->usize {
    _to_u64(data, index) as usize
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn test_function27(_param0 :usize ,_param1 :usize ,mut _param2 :u32 ,mut _param3 :u32) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _local0 = <usize as subtle::ConstantTimeEq>::ct_ne(_local0_param0_helper1, _local0_param1_helper1);
    let _local1 = <subtle::Choice as std::ops::Not>::not(_local0);
    let _local2_param0_helper1 = &mut (_param2);
    let _local2_param1_helper1 = &mut (_param3);
    let _ = <u32 as subtle::ConditionallySelectable>::conditional_swap(_local2_param0_helper1, _local2_param1_helper1, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 24 {return;}
        let _param0 = _to_usize(data, 0);
        let _param1 = _to_usize(data, 8);
        let _param2 = _to_u32(data, 16);
        let _param3 = _to_u32(data, 20);
        test_function27(_param0 ,_param1 ,_param2 ,_param3);
    });
}
