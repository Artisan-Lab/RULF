#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function181(_param0 :u8) {
    let _local0 = <toml::Value as std::convert::From::<u8>>::from(_param0);
    let _: toml::ser::Error = <toml::ser::Error as serde::ser::Error>::custom(_local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_u8(data, 0);
        test_function181(_param0);
    });
}
