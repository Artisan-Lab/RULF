#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn test_function91(_param0 :monero::cryptonote::subaddress::Index ,_param1 :monero::cryptonote::subaddress::Index) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <monero::cryptonote::subaddress::Index as std::cmp::PartialEq::<monero::cryptonote::subaddress::Index>>::eq(_local0_param0_helper1, _local0_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 16 {return;}
        let _param0 = monero::cryptonote::subaddress::Index{major: _to_u32(data, 0), minor: _to_u32(data, 4)};
        let _param1 = monero::cryptonote::subaddress::Index{major: _to_u32(data, 8), minor: _to_u32(data, 12)};
        test_function91(_param0 ,_param1);
    });
}
