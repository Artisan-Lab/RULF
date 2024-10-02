#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_str(data:&[u8], start_index: usize, end_index: usize)->&str {
    let data_slice = &data[start_index..end_index];
    use std::str;
    match str::from_utf8(data_slice) {
        Ok(s)=>s,
        Err(_)=>{
            use std::process;
            process::exit(0);
        }
    }
}

fn test_function22(_param0 :&str) {
    let mut _local0 = <cookie::Cookie::<'_> as std::convert::From::<&str>>::from(_param0);
    let _local1_param0_helper1 = &mut (_local0);
    let _local1 = <cookie::Cookie::<'_> as std::convert::AsMut::<cookie::Cookie::<'_>>>::as_mut(_local1_param0_helper1);
    let _ = cookie::Cookie::<'_>::unset_domain(_local1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 0) / 1;
        let _param0 = _to_str(data, 0 + 0 * dynamic_length, data.len());
        test_function22(_param0);
    });
}
