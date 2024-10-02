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

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn _to_usize(data:&[u8], index:usize)->usize {
    _to_u64(data, index) as usize
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

fn test_function104(_param0 :bool ,_param1 :usize) {
    let _local0 = <toml::Value as std::convert::From::<bool>>::from(_param0);
    let mut _local1 = <toml::Value as serde::de::IntoDeserializer::<'_, toml::de::Error>>::into_deserializer(_local0);
    let _local2_param0_helper1 = &mut (_local1);
    let _: std::option::Option::<&mut toml::Value> = toml::Value::get_mut(_local2_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 9 {return;}
        let _param0 = _to_bool(data, 0);
        let _param1 = _to_usize(data, 1);
        test_function104(_param0 ,_param1);
    });
}
