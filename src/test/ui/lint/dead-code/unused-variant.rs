#![deny(dead_code)]

#[derive(Clone)]
enum Enum {
    Variant1, //~ ERROR: variant `Variant1` is never constructed
    Variant2,
}

fn main() {
    let e = Enum::Variant2;
    e.clone();
}
