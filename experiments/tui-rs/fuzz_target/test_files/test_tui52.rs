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

fn test_function52(_param0 :bool) {
    let mut _local0 = tui::style::Modifier::empty();
    let _local1 = tui::style::Modifier::all();
    let _local2_param0_helper1 = &mut (_local0);
    let _ = tui::style::Modifier::set(_local2_param0_helper1, _local1, _param0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 1 {return;}
        let _param0 = _to_bool(data, 0);
        test_function52(_param0);
    });
}
