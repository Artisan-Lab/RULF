#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
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

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function19(_param0 :u8 ,mut _param1 :u128 ,mut _param2 :u128) {
    let _local0 = <subtle::Choice as std::convert::From::<u8>>::from(_param0);
    let _local1 = <subtle::Choice as std::ops::Not>::not(_local0);
    let _local2_param0_helper1 = &mut (_param1);
    let _local2_param1_helper1 = &mut (_param2);
    let _ = <u128 as subtle::ConditionallySelectable>::conditional_swap(_local2_param0_helper1, _local2_param1_helper1, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 33 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_u128(data, 1);
        let _param2 = _to_u128(data, 17);
        test_function19(_param0 ,_param1 ,_param2);
    });
}
