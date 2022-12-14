// unit-test: InstCombine
// ignore-wasm32 compiled with panic=abort by default

// EMIT_MIR combine_clone_of_primitives.{impl#0}-clone.InstCombine.diff

#[derive(Clone)]
struct MyThing<T> {
    v: T,
    i: u64,
    a: [f32; 3],
}

fn main() {
    let x = MyThing::<i16> { v: 2, i: 3, a: [0.0; 3] };
    let y = x.clone();

    assert_eq!(y.v, 2);
    assert_eq!(y.i, 3);
    assert_eq!(y.a, [0.0; 3]);
}
