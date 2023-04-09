//! Proc Macro Expander stub

use base_db::{CrateId, ProcMacroExpansionError, ProcMacroId, ProcMacroKind};
use stdx::never;

use crate::{db::AstDatabase, ExpandError, ExpandResult};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ProcMacroExpander {
    krate: CrateId,
    proc_macro_id: Option<ProcMacroId>,
}

impl ProcMacroExpander {
    pub fn new(krate: CrateId, proc_macro_id: ProcMacroId) -> Self {
        Self { krate, proc_macro_id: Some(proc_macro_id) }
    }

    pub fn dummy(krate: CrateId) -> Self {
        // FIXME: Should store the name for better errors
        Self { krate, proc_macro_id: None }
    }

    pub fn is_dummy(&self) -> bool {
        self.proc_macro_id.is_none()
    }

    pub fn expand(
        self,
        db: &dyn AstDatabase,
        calling_crate: CrateId,
        tt: &tt::Subtree,
        attr_arg: Option<&tt::Subtree>,
    ) -> ExpandResult<tt::Subtree> {
        match self.proc_macro_id {
            Some(id) => {
                let krate_graph = db.crate_graph();
                let proc_macros = match &krate_graph[self.krate].proc_macro {
                    Ok(proc_macros) => proc_macros,
                    Err(_) => {
                        never!("Non-dummy expander even though there are no proc macros");
                        return ExpandResult::only_err(ExpandError::Other("Internal error".into()));
                    }
                };
                let proc_macro = match proc_macros.get(id.0 as usize) {
                    Some(proc_macro) => proc_macro,
                    None => {
                        never!(
                            "Proc macro index out of bounds: the length is {} but the index is {}",
                            proc_macros.len(),
                            id.0
                        );
                        return ExpandResult::only_err(ExpandError::Other("Internal error".into()));
                    }
                };

                // Proc macros have access to the environment variables of the invoking crate.
                let env = &krate_graph[calling_crate].env;
                match proc_macro.expander.expand(tt, attr_arg, env) {
                    Ok(t) => ExpandResult::ok(t),
                    Err(err) => match err {
                        // Don't discard the item in case something unexpected happened while expanding attributes
                        ProcMacroExpansionError::System(text)
                            if proc_macro.kind == ProcMacroKind::Attr =>
                        {
                            ExpandResult {
                                value: tt.clone(),
                                err: Some(ExpandError::Other(text.into())),
                            }
                        }
                        ProcMacroExpansionError::System(text)
                        | ProcMacroExpansionError::Panic(text) => {
                            ExpandResult::only_err(ExpandError::Other(text.into()))
                        }
                    },
                }
            }
            None => ExpandResult::only_err(ExpandError::UnresolvedProcMacro(self.krate)),
        }
    }
}
