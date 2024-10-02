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

fn test_function145(_param0 :toml_datetime::Date) {
    let _local0: toml::de::Error = <toml::de::Error as serde::de::Error>::custom(_param0);
    let _local1: toml::de::Error = <toml::de::Error as serde::de::Error>::custom(_local0);
    let _local2_param0_helper1 = &(_local1);
    let _ = toml::de::Error::span(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 4 {return;}
        let _param0 = toml_datetime::Date{year: _to_u16(data, 0), month: _to_u8(data, 2), day: _to_u8(data, 3)};
        test_function145(_param0);
    });
}
