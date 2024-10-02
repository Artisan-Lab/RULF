#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function215(_param0 :i8) {
    let _local0 = <toml::Value as std::convert::From::<i8>>::from(_param0);
    let _: toml::de::Error = <toml::de::Error as serde::de::Error>::custom(_local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_i8(data, 0);
        test_function215(_param0);
    });
}
