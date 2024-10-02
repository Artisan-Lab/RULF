#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function70(_param0 :cookie::prefix::Secure ,_param1 :cookie::prefix::Host) {
    let _local0 = <cookie::CookieJar as std::default::Default>::default();
    let _local1_param0_helper1 = &(_local0);
    let mut _local1: cookie::prefix::PrefixedJar::<cookie::prefix::Secure, &cookie::CookieJar> = cookie::CookieJar::prefixed(_local1_param0_helper1, _param0);
    let _local2_param0_helper1 = &mut (_local1);
    let _local2_param1_helper1 = &(_param1);
    let _ = cookie::prefix::PrefixedJar::<cookie::prefix::Secure, &cookie::CookieJar>::add_original(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = cookie::prefix::Secure{};
        let _param1 = cookie::prefix::Host{};
        test_function70(_param0 ,_param1);
    });
}
