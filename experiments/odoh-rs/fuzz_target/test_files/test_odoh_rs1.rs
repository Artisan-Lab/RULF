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

fn test_function1(_param0 :u16 ,_param1 :u16 ,_param2 :u16 ,_param3 :&[u8]) {
    let _local0 = odoh_rs::ObliviousDoHKeyPair::from_parameters(_param0, _param1, _param2, _param3);
    let _local1_param0_helper1 = &(_local0);
    let _local1 = odoh_rs::ObliviousDoHKeyPair::public(_local1_param0_helper1);
    let _ = odoh_rs::ObliviousDoHConfigContents::identifier(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 7 {return;}
        let dynamic_length = (data.len() - 6) / 1;
        let _param0 = _to_u16(data, 0);
        let _param1 = _to_u16(data, 2);
        let _param2 = _to_u16(data, 4);
        let _param3 = _to_slice::<u8>(data, 6 + 0 * dynamic_length, data.len());
        test_function1(_param0 ,_param1 ,_param2 ,_param3);
    });
}
