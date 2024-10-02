#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn test_function275(_param0 :i8) {
    let _local0 = <toml::Value as std::convert::From::<i8>>::from(_param0);
    let _local1_param0_helper1 = &(_local0);
    let _: std::result::Result::<std::string::String, toml::ser::Error> = toml::to_string(_local1_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_i8(data, 0);
        test_function275(_param0);
    });
}
