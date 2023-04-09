use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{CrateNum, DefId, CRATE_DEF_ID};
use rustc_middle::middle::privacy::{EffectiveVisibilities, Level};
use rustc_middle::ty::{TyCtxt, Visibility};

// FIXME: this may not be exhaustive, but is sufficient for rustdocs current uses

/// Similar to `librustc_privacy::EmbargoVisitor`, but also takes
/// specific rustdoc annotations into account (i.e., `doc(hidden)`)
pub(crate) struct LibEmbargoVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    // Effective visibilities for reachable nodes
    effective_visibilities: &'a mut EffectiveVisibilities<DefId>,
    // Previous level, None means unreachable
    prev_level: Option<Level>,
    // Keeps track of already visited modules, in case a module re-exports its parent
    visited_mods: FxHashSet<DefId>,
}

impl<'a, 'tcx> LibEmbargoVisitor<'a, 'tcx> {
    pub(crate) fn new(cx: &'a mut crate::core::DocContext<'tcx>) -> LibEmbargoVisitor<'a, 'tcx> {
        LibEmbargoVisitor {
            tcx: cx.tcx,
            effective_visibilities: &mut cx.cache.effective_visibilities,
            prev_level: Some(Level::Direct),
            visited_mods: FxHashSet::default(),
        }
    }

    pub(crate) fn visit_lib(&mut self, cnum: CrateNum) {
        let did = cnum.as_def_id();
        self.update(did, Some(Level::Direct));
        self.visit_mod(did);
    }

    // Updates node level and returns the updated level
    fn update(&mut self, did: DefId, level: Option<Level>) -> Option<Level> {
        let is_hidden = self.tcx.is_doc_hidden(did);

        let old_level = self.effective_visibilities.public_at_level(did);
        // Visibility levels can only grow
        if level > old_level && !is_hidden {
            self.effective_visibilities.set_public_at_level(
                did,
                || Visibility::Restricted(CRATE_DEF_ID),
                level.unwrap(),
            );
            level
        } else {
            old_level
        }
    }

    pub(crate) fn visit_mod(&mut self, def_id: DefId) {
        if !self.visited_mods.insert(def_id) {
            return;
        }

        for item in self.tcx.module_children(def_id).iter() {
            if let Some(def_id) = item.res.opt_def_id() {
                if self.tcx.def_key(def_id).parent.map_or(false, |d| d == def_id.index)
                    || item.vis.is_public()
                {
                    self.visit_item(item.res);
                }
            }
        }
    }

    fn visit_item(&mut self, res: Res<!>) {
        let def_id = res.def_id();
        let vis = self.tcx.visibility(def_id);
        let inherited_item_level = if vis.is_public() { self.prev_level } else { None };

        let item_level = self.update(def_id, inherited_item_level);

        if let Res::Def(DefKind::Mod, _) = res {
            let orig_level = self.prev_level;

            self.prev_level = item_level;
            self.visit_mod(def_id);
            self.prev_level = orig_level;
        }
    }
}
