use rustc_hir::def_id::DefId;

#[derive(Hash, Eq, Copy, PartialEq, Clone, Debug)]
pub(crate) enum ImplId {
    Unknown,
    Id(DefId),
}

impl ImplId {}

/* impl PartialEq for ImplId{
    fn eq
} */
