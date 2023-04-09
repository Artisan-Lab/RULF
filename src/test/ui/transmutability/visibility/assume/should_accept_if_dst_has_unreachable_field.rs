//! If visibility is assumed, a transmutation should be accepted even if the
//! destination type contains an unreachable field (e.g., a public field with a
//! private type). (This rule is distinct from type privacy, which still may
//! forbid naming such types.)

#![crate_type = "lib"]
#![feature(transmutability)]
#![allow(dead_code)]

mod assert {
    use std::mem::{Assume, BikeshedIntrinsicFrom};

    pub fn is_transmutable<Src, Dst, Context>()
    where
        Dst: BikeshedIntrinsicFrom<Src, Context, { Assume::SAFETY }>
        // safety IS assumed --------------------^^^^^^^^^^^^^^^^^^
    {}
}

mod src {
    #[repr(C)] pub(self) struct Zst;

    #[repr(C)] pub(in super) struct Src {
        pub(self) field: Zst,
    }
}

mod dst {
    #[repr(C)] pub(self) struct Zst; // <- unreachable type

    #[repr(C)] pub(in super) struct Dst {
        pub(in super) field: Zst, //~ ERROR private type
    }
}

fn test() {
    struct Context;
    assert::is_transmutable::<src::Src, dst::Dst, Context>();
}
