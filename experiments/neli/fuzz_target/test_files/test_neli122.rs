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

fn test_function122(_param0 :u16 ,_param1 :u16) {
    let mut _local0 = <neli::consts::nl::NlmF as std::convert::From::<u16>>::from(_param0);
    let _local1 = <neli::consts::nl::NlmF as std::convert::From::<u16>>::from(_param1);
    let _local2_param0_helper1 = &mut (_local0);
    let _ = <neli::consts::nl::NlmF as std::ops::BitXorAssign::<neli::consts::nl::NlmF>>::bitxor_assign(_local2_param0_helper1, _local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = _to_u16(data, 0);
        let _param1 = _to_u16(data, 2);
        test_function122(_param0 ,_param1);
    });
}
