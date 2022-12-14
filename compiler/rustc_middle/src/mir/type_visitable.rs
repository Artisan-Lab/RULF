//! `TypeVisitable` implementations for MIR types

use super::*;

impl<'tcx, R: Idx, C: Idx> TypeVisitable<'tcx> for BitMatrix<R, C> {
    fn visit_with<V: TypeVisitor<'tcx>>(&self, _: &mut V) -> ControlFlow<V::BreakTy> {
        ControlFlow::CONTINUE
    }
}
