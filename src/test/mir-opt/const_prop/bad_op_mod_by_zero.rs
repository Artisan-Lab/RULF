// EMIT_MIR bad_op_mod_by_zero.main.ConstProp.diff
#[allow(unconditional_panic)]
fn main() {
    let y = 0;
    let _z = 1 % y;
}
