#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function212(_param0 :i8) {
    let _local0 = <toml::Value as std::convert::From::<i8>>::from(_param0);
    let _: std::result::Result::<toml::Table, toml::ser::Error> = toml::Table::try_from(_local0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_i8(data, 0);
        test_function212(_param0);
    });
}
