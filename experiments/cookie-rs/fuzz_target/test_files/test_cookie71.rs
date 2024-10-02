#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn test_function71(_param0 :cookie::prefix::Host) {
    let _local0 = cookie::CookieJar::new();
    let _local1_param0_helper1 = &(_local0);
    let _: cookie::prefix::PrefixedJar::<cookie::prefix::Host, &cookie::CookieJar> = cookie::CookieJar::prefixed(_local1_param0_helper1, _param0);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 0 {return;}
        let _param0 = cookie::prefix::Host{};
        test_function71(_param0);
    });
}
