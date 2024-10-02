#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn test_function10(_param0 :cpp_demangle::ast::CvQualifiers) {
    let mut _local0 = std::collections::hash_map::DefaultHasher::new();
    let _local1_param0_helper1 = &(_param0);
    let _local1_param1_helper1 = &mut (_local0);
    let _: () = <cpp_demangle::ast::CvQualifiers as std::hash::Hash>::hash(_local1_param0_helper1, _local1_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 3 {return;}
        let _param0 = cpp_demangle::ast::CvQualifiers{restrict: _to_bool(data, 0), volatile: _to_bool(data, 1), const_: _to_bool(data, 2)};
        test_function10(_param0);
    });
}
