#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

fn test_function14(_param0 :&[char] ,_param1 :u16 ,_param2 :u16) {
    let _local0: tui::widgets::Row::<'_> = tui::widgets::Row::<'_>::new(_param0);
    let _local1 = tui::widgets::Row::<'_>::height(_local0, _param1);
    let _ = tui::widgets::Row::<'_>::bottom_margin(_local1, _param2);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 8 {return;}
        let dynamic_length = (data.len() - 4) / 1;
        let _param0 = _to_slice::<char>(data, 4 + 0 * dynamic_length, data.len());
        let _param1 = _to_u16(data, 0);
        let _param2 = _to_u16(data, 2);
        test_function14(_param0 ,_param1 ,_param2);
    });
}
