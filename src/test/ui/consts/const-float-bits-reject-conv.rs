// compile-flags: -Zmir-opt-level=0
#![feature(const_float_bits_conv)]
#![feature(const_float_classify)]

// Don't promote
const fn nop<T>(x: T) -> T { x }

macro_rules! const_assert {
    ($a:expr) => {
        {
            const _: () = assert!($a);
            assert!(nop($a));
        }
    };
    ($a:expr, $b:expr) => {
        {
            const _: () = assert!($a == $b);
            assert_eq!(nop($a), nop($b));
        }
    };
}

fn f32() {
    // Check that NaNs roundtrip their bits regardless of signalingness
    // 0xA is 0b1010; 0x5 is 0b0101 -- so these two together clobbers all the mantissa bits
    // ...actually, let's just check that these break. :D
    const MASKED_NAN1: u32 = f32::NAN.to_bits() ^ 0x002A_AAAA;
    const MASKED_NAN2: u32 = f32::NAN.to_bits() ^ 0x0055_5555;

    const_assert!(f32::from_bits(MASKED_NAN1).is_nan());
    //~^ ERROR evaluation of constant value failed
    const_assert!(f32::from_bits(MASKED_NAN1).is_nan());
    //~^ ERROR evaluation of constant value failed

    // LLVM does not guarantee that loads and stores of NaNs preserve their exact bit pattern.
    // In practice, this seems to only cause a problem on x86, since the most widely used calling
    // convention mandates that floating point values are returned on the x87 FPU stack. See #73328.
    if !cfg!(target_arch = "x86") {
        const_assert!(f32::from_bits(MASKED_NAN1).to_bits(), MASKED_NAN1);
        //~^ ERROR evaluation of constant value failed
        const_assert!(f32::from_bits(MASKED_NAN2).to_bits(), MASKED_NAN2);
        //~^ ERROR evaluation of constant value failed
    }
}

fn f64() {
    // Check that NaNs roundtrip their bits regardless of signalingness
    // 0xA is 0b1010; 0x5 is 0b0101 -- so these two together clobbers all the mantissa bits
    // ...actually, let's just check that these break. :D
    const MASKED_NAN1: u64 = f64::NAN.to_bits() ^ 0x000A_AAAA_AAAA_AAAA;
    const MASKED_NAN2: u64 = f64::NAN.to_bits() ^ 0x0005_5555_5555_5555;

    const_assert!(f64::from_bits(MASKED_NAN1).is_nan());
    //~^ ERROR evaluation of constant value failed
    const_assert!(f64::from_bits(MASKED_NAN1).is_nan());
    //~^ ERROR evaluation of constant value failed

    // See comment above.
    if !cfg!(target_arch = "x86") {
        const_assert!(f64::from_bits(MASKED_NAN1).to_bits(), MASKED_NAN1);
        //~^ ERROR evaluation of constant value failed
        const_assert!(f64::from_bits(MASKED_NAN2).to_bits(), MASKED_NAN2);
        //~^ ERROR evaluation of constant value failed
    }
}

fn main() {
    f32();
    f64();
}
