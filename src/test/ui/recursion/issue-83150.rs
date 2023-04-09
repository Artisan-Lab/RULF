// build-fail
// compile-flags: -Copt-level=0
//~^^ ERROR overflow evaluating the requirement

fn main() {
    let mut iter = 0u8..1;
    func(&mut iter)
}

fn func<T: Iterator<Item = u8>>(iter: &mut T) { //~ WARN function cannot return without recursing
    func(&mut iter.map(|x| x + 1))
}
