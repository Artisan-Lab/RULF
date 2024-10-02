#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function142(_param0 :toml_datetime::DatetimeParseError) {
    let _local0: toml::de::Error = <toml::de::Error as serde::de::Error>::custom(_param0);
    let _local1: toml::ser::Error = <toml::ser::Error as serde::ser::Error>::custom(_local0);
    let _: toml::ser::Error = <toml::ser::Error as serde::ser::Error>::custom(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = toml_datetime::DatetimeParseError{};
        test_function142(_param0);
    });
}
