#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
}

fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}

fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}

fn test_function0(_param0 :i64 ,_param1 :&[u8]) {
    let _local0_param0_helper1 = &(_param0);
    let _local0 = <i64 as prost::Message>::encode_to_vec(_local0_param0_helper1);
    let _local1_param0_helper1 = &(_local0);
    let mut _local1 = <std::vec::Vec::<u8> as prost::Message>::encode_to_vec(_local1_param0_helper1);
    let _local2_param0_helper1 = &mut (_local1);
    let _: std::result::Result::<(), prost::DecodeError> = <std::vec::Vec::<u8> as prost::Message>::merge(_local2_param0_helper1, _param1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 9 {return;}
        let dynamic_length = (data.len() - 8) / 1;
        let _param0 = _to_i64(data, 0);
        let _param1 = _to_slice::<u8>(data, 8 + 0 * dynamic_length, data.len());
        test_function0(_param0 ,_param1);
    });
}
