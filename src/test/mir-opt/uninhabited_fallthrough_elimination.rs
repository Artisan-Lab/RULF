enum Empty {}

enum S {
    A(Empty),
    B,
    C,
}

use S::*;

// EMIT_MIR uninhabited_fallthrough_elimination.keep_fallthrough.UninhabitedEnumBranching.diff
fn keep_fallthrough(s: S) -> u32 {
    match s {
        A(_) => 1,
        B => 2,
        _ => 3,
    }
}

// EMIT_MIR uninhabited_fallthrough_elimination.eliminate_fallthrough.UninhabitedEnumBranching.diff
fn eliminate_fallthrough(s: S) -> u32 {
    match s {
        C => 1,
        B => 2,
        _ => 3,
    }
}

fn main() {
    keep_fallthrough(B);
    eliminate_fallthrough(B);
}
