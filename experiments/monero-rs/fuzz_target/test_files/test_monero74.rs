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

fn test_function74(_param0 :monero::cryptonote::subaddress::Index) {
    let _local0 = <monero::blockdata::transaction::Transaction as std::default::Default>::default();
    let _local1_param0_helper1 = &(_local0);
    let _local1 = <monero::blockdata::transaction::Transaction as monero::cryptonote::hash::Hashable>::hash_to_scalar(_local1_param0_helper1);
    let _local2_param0_helper1 = &(_local1);
    let _ = monero::cryptonote::subaddress::get_secret_scalar(_local2_param0_helper1, _param0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 8 {return;}
        let _param0 = monero::cryptonote::subaddress::Index{major: _to_u32(data, 0), minor: _to_u32(data, 4)};
        test_function74(_param0);
    });
}
