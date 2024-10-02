#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn test_function6(_param0 :u8 ,_param1 :u8) {
    let mut _local0 = std::collections::hash_map::DefaultHasher::new();
    let _local1: genmesh::Line::<u8> = genmesh::Line::<u8>::new(_param0, _param1);
    let _local2_param0_helper1 = &(_local1);
    let _local2_param1_helper1 = &mut (_local0);
    let _: () = <genmesh::Line::<u8> as std::hash::Hash>::hash(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 2 {return;}
        let _param0 = _to_u8(data, 0);
        let _param1 = _to_u8(data, 1);
        test_function6(_param0 ,_param1);
    });
}
