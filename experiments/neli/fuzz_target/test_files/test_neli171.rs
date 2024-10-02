#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function171(_param0 :u8) {
    let _local0 = <neli::consts::rtnl::Ntf as bitflags::traits::Flags>::from_bits_retain(_param0);
    let _local1 = <neli::rtnl::NdmsgBuilder as std::default::Default>::default();
    let _ = neli::rtnl::NdmsgBuilder::ndm_flags(_local1, _local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function171(_param0);
    });
}
