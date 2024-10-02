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

fn test_function12(_param0 :cpp_demangle::ast::CvQualifiers ,_param1 :cpp_demangle::ast::CvQualifiers) {
    let _local0_param0_helper1 = &(_param0);
    let _local0_param1_helper1 = &(_param1);
    let _ = <cpp_demangle::ast::CvQualifiers as std::cmp::PartialEq::<cpp_demangle::ast::CvQualifiers>>::eq(_local0_param0_helper1, _local0_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 6 {return;}
        let _param0 = cpp_demangle::ast::CvQualifiers{restrict: _to_bool(data, 0), volatile: _to_bool(data, 1), const_: _to_bool(data, 2)};
        let _param1 = cpp_demangle::ast::CvQualifiers{restrict: _to_bool(data, 3), volatile: _to_bool(data, 4), const_: _to_bool(data, 5)};
        test_function12(_param0 ,_param1);
    });
}
