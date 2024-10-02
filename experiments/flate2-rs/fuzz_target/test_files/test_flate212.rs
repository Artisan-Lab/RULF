#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn test_function12(_param0 :u32 ,_param1 :bool ,_param2 :&[u8]) {
    let _local0 = flate2::Compression::new(_param0);
    let _local1 = flate2::Compress::new(_local0, _param1);
    let _local2: flate2::bufread::ZlibEncoder::<&[u8]> = flate2::bufread::ZlibEncoder::<&[u8]>::new_with_compress(_param2, _local1);
    let _: &[u8] = flate2::bufread::ZlibEncoder::<&[u8]>::into_inner(_local2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 6 {return;}
        let dynamic_length = (data.len() - 5) / 1;
        let _param0 = _to_u32(data, 0);
        let _param1 = _to_bool(data, 4);
        let _param2 = _to_slice::<u8>(data, 5 + 0 * dynamic_length, data.len());
        test_function12(_param0 ,_param1 ,_param2);
    });
}
