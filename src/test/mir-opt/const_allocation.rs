// ignore-endian-big
// EMIT_MIR_FOR_EACH_BIT_WIDTH
static FOO: &[(Option<i32>, &[&str])] =
    &[(None, &[]), (None, &["foo", "bar"]), (Some(42), &["meh", "mop", "möp"])];

// EMIT_MIR const_allocation.main.ConstProp.after.mir
fn main() {
    FOO;
}
