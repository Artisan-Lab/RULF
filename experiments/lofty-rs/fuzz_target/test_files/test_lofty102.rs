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

fn test_function102(_param0 :u32 ,_param1 :u32 ,_param2 :u32 ,_param3 :u8 ,_param4 :u8) {
    let _local0 = <lofty::mp4::Mp4Properties as std::default::Default>::default();
    let _local1 = <lofty::FileProperties as std::convert::From::<lofty::mp4::Mp4Properties>>::from(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _local2 = lofty::FileProperties::duration(_local2_param0_helper1);
    let _local3 = <lofty::mp4::Mp4Properties as std::default::Default>::default();
    let _local4 = <lofty::FileProperties as std::convert::From::<lofty::mp4::Mp4Properties>>::from(_local3);
    let _local5_param0_helper1 = &(_local4);
    let _local5 = lofty::FileProperties::channel_mask(_local5_param0_helper1);
    let _local6_param1_helper1 = Some(_param0);
    let _local6_param2_helper1 = Some(_param1);
    let _local6_param3_helper1 = Some(_param2);
    let _local6_param4_helper1 = Some(_param3);
    let _local6_param5_helper1 = Some(_param4);
    let _ = lofty::FileProperties::new(_local2, _local6_param1_helper1, _local6_param2_helper1, _local6_param3_helper1, _local6_param4_helper1, _local6_param5_helper1, _local5);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 14 {return;}
        let _param0 = _to_u32(data, 0);
        let _param1 = _to_u32(data, 4);
        let _param2 = _to_u32(data, 8);
        let _param3 = _to_u8(data, 12);
        let _param4 = _to_u8(data, 13);
        test_function102(_param0 ,_param1 ,_param2 ,_param3 ,_param4);
    });
}
