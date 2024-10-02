#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function74(_param0 :cookie::prefix::Host ,_param1 :cookie::prefix::Host) {
    let mut _local0 = cookie::CookieJar::new();
    let _local1_param0_helper1 = &mut (_local0);
    let mut _local1: cookie::prefix::PrefixedJar::<cookie::prefix::Host, &mut cookie::CookieJar> = cookie::CookieJar::prefixed_mut(_local1_param0_helper1, _param0);
    let _local2_param0_helper1 = &mut (_local1);
    let _local2_param1_helper1 = &(_param1);
    let _ = cookie::prefix::PrefixedJar::<cookie::prefix::Host, &mut cookie::CookieJar>::remove(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = cookie::prefix::Host{};
        let _param1 = cookie::prefix::Host{};
        test_function74(_param0 ,_param1);
    });
}
