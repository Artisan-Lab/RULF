/* use crate::clean;
use crate::{
    clean::{Item, Struct},
    format::cache::Cache,
};
use rustc_hir::def_id::DefId;
struct ApiType {
    id: DefId,
    trait_impl: FxHashSet<DefId>,
}
impl ApiType {
    fn from(item: Item, cache: &Cache) -> ApiStruct {
        assert!(matches!(item.kind, StructItem(_)));
        assert!(item.item_id.as_def_id().is_some());
        if let 
        ApiStruct { id: item.item_id.as_def_id().unwrap() }
    }
}
 */