//! The presence of an unreachable source type (i.e., the source type is
//! private) does not affect transmutability. (This rule is distinct from type
//! privacy, which still may forbid naming such types.)

#![crate_type = "lib"]
#![feature(transmutability)]
#![allow(dead_code)]

mod assert {
    use std::mem::BikeshedIntrinsicFrom;

    pub fn is_transmutable<Src, Dst, Context>()
    where
        Dst: BikeshedIntrinsicFrom<Src, Context> // safety is NOT assumed
    {}
}

mod src {
    #[repr(C)] pub(in super) struct Zst;

    // unreachable type
    #[repr(C)] pub(self) struct Src {
        pub(in super) field: Zst,
    }
}

mod dst {
    #[repr(C)] pub(in super) struct Zst;

    #[repr(C)] pub(in super) struct Dst {
        pub(in super) field: Zst,
    }
}

fn test() {
    struct Context;
    assert::is_transmutable::<src::Src, dst::Dst, Context>(); //~ ERROR `Src` is private
}
