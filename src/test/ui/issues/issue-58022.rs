pub trait Foo: Sized {
    const SIZE: usize;

    fn new(slice: &[u8; Foo::SIZE]) -> Self;
    //~^ ERROR: E0790
}

pub struct Bar<T: ?Sized>(T);

impl Bar<[u8]> {
    const SIZE: usize = 32;

    fn new(slice: &[u8; Self::SIZE]) -> Self {
        Foo(Box::new(*slice))
        //~^ ERROR: expected function, tuple struct or tuple variant, found trait `Foo`
    }
}

fn main() {}
