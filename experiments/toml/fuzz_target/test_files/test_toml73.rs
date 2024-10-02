#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
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

fn test_function73(_param0 :toml_datetime::Date ,_param1 :toml_datetime::Time) {
    let _local0: toml::ser::Error = <toml::ser::Error as serde::ser::Error>::custom(_param0);
    let _local1: toml::ser::Error = <toml::ser::Error as serde::ser::Error>::custom(_param1);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _ = <toml::ser::Error as std::cmp::PartialEq::<toml::ser::Error>>::eq(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 11 {return;}
        let _param0 = toml_datetime::Date{year: _to_u16(data, 0), month: _to_u8(data, 2), day: _to_u8(data, 3)};
        let _param1 = toml_datetime::Time{hour: _to_u8(data, 4), minute: _to_u8(data, 5), second: _to_u8(data, 6), nanosecond: _to_u32(data, 7)};
        test_function73(_param0 ,_param1);
    });
}
