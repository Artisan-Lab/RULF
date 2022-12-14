//! Code that handles "type-outlives" constraints like `T: 'a`. This
//! is based on the `push_outlives_components` function defined in rustc_infer,
//! but it adds a bit of heuristics on top, in particular to deal with
//! associated types and projections.
//!
//! When we process a given `T: 'a` obligation, we may produce two
//! kinds of constraints for the region inferencer:
//!
//! - Relationships between inference variables and other regions.
//!   For example, if we have `&'?0 u32: 'a`, then we would produce
//!   a constraint that `'a <= '?0`.
//! - "Verifys" that must be checked after inferencing is done.
//!   For example, if we know that, for some type parameter `T`,
//!   `T: 'a + 'b`, and we have a requirement that `T: '?1`,
//!   then we add a "verify" that checks that `'?1 <= 'a || '?1 <= 'b`.
//!   - Note the difference with the previous case: here, the region
//!     variable must be less than something else, so this doesn't
//!     affect how inference works (it finds the smallest region that
//!     will do); it's just a post-condition that we have to check.
//!
//! **The key point is that once this function is done, we have
//! reduced all of our "type-region outlives" obligations into relationships
//! between individual regions.**
//!
//! One key input to this function is the set of "region-bound pairs".
//! These are basically the relationships between type parameters and
//! regions that are in scope at the point where the outlives
//! obligation was incurred. **When type-checking a function,
//! particularly in the face of closures, this is not known until
//! regionck runs!** This is because some of those bounds come
//! from things we have yet to infer.
//!
//! Consider:
//!
//! ```
//! fn bar<T>(a: T, b: impl for<'a> Fn(&'a T)) {}
//! fn foo<T>(x: T) {
//!     bar(x, |y| { /* ... */})
//!          // ^ closure arg
//! }
//! ```
//!
//! Here, the type of `y` may involve inference variables and the
//! like, and it may also contain implied bounds that are needed to
//! type-check the closure body (e.g., here it informs us that `T`
//! outlives the late-bound region `'a`).
//!
//! Note that by delaying the gathering of implied bounds until all
//! inference information is known, we may find relationships between
//! bound regions and other regions in the environment. For example,
//! when we first check a closure like the one expected as argument
//! to `foo`:
//!
//! ```
//! fn foo<U, F: for<'a> FnMut(&'a U)>(_f: F) {}
//! ```
//!
//! the type of the closure's first argument would be `&'a ?U`. We
//! might later infer `?U` to something like `&'b u32`, which would
//! imply that `'b: 'a`.

use crate::infer::outlives::components::{push_outlives_components, Component};
use crate::infer::outlives::env::OutlivesEnvironment;
use crate::infer::outlives::env::RegionBoundPairs;
use crate::infer::outlives::verify::VerifyBoundCx;
use crate::infer::{
    self, GenericKind, InferCtxt, RegionObligation, SubregionOrigin, UndoLog, VerifyBound,
};
use crate::traits::{ObligationCause, ObligationCauseCode};
use rustc_data_structures::undo_log::UndoLogs;
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::ConstraintCategory;
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{self, Region, SubstsRef, Ty, TyCtxt, TypeVisitable};
use smallvec::smallvec;

impl<'tcx> InferCtxt<'tcx> {
    /// Registers that the given region obligation must be resolved
    /// from within the scope of `body_id`. These regions are enqueued
    /// and later processed by regionck, when full type information is
    /// available (see `region_obligations` field for more
    /// information).
    #[instrument(level = "debug", skip(self))]
    pub fn register_region_obligation(&self, obligation: RegionObligation<'tcx>) {
        let mut inner = self.inner.borrow_mut();
        inner.undo_log.push(UndoLog::PushRegionObligation);
        inner.region_obligations.push(obligation);
    }

    pub fn register_region_obligation_with_cause(
        &self,
        sup_type: Ty<'tcx>,
        sub_region: Region<'tcx>,
        cause: &ObligationCause<'tcx>,
    ) {
        debug!(?sup_type, ?sub_region, ?cause);
        let origin = SubregionOrigin::from_obligation_cause(cause, || {
            infer::RelateParamBound(
                cause.span,
                sup_type,
                match cause.code().peel_derives() {
                    ObligationCauseCode::BindingObligation(_, span)
                    | ObligationCauseCode::ExprBindingObligation(_, span, ..) => Some(*span),
                    _ => None,
                },
            )
        });

        self.register_region_obligation(RegionObligation { sup_type, sub_region, origin });
    }

    /// Trait queries just want to pass back type obligations "as is"
    pub fn take_registered_region_obligations(&self) -> Vec<RegionObligation<'tcx>> {
        std::mem::take(&mut self.inner.borrow_mut().region_obligations)
    }

    /// NOTE: Prefer using [`InferCtxt::check_region_obligations_and_report_errors`]
    /// instead of calling this directly.
    ///
    /// Process the region obligations that must be proven (during
    /// `regionck`) for the given `body_id`, given information about
    /// the region bounds in scope and so forth. This function must be
    /// invoked for all relevant body-ids before region inference is
    /// done (or else an assert will fire).
    ///
    /// See the `region_obligations` field of `InferCtxt` for some
    /// comments about how this function fits into the overall expected
    /// flow of the inferencer. The key point is that it is
    /// invoked after all type-inference variables have been bound --
    /// towards the end of regionck. This also ensures that the
    /// region-bound-pairs are available (see comments above regarding
    /// closures).
    ///
    /// # Parameters
    ///
    /// - `region_bound_pairs_map`: the set of region bounds implied by
    ///   the parameters and where-clauses. In particular, each pair
    ///   `('a, K)` in this list tells us that the bounds in scope
    ///   indicate that `K: 'a`, where `K` is either a generic
    ///   parameter like `T` or a projection like `T::Item`.
    /// - `param_env` is the parameter environment for the enclosing function.
    /// - `body_id` is the body-id whose region obligations are being
    ///   processed.
    #[instrument(level = "debug", skip(self, region_bound_pairs))]
    pub fn process_registered_region_obligations(
        &self,
        region_bound_pairs: &RegionBoundPairs<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
    ) {
        assert!(
            !self.in_snapshot.get(),
            "cannot process registered region obligations in a snapshot"
        );

        let my_region_obligations = self.take_registered_region_obligations();

        for RegionObligation { sup_type, sub_region, origin } in my_region_obligations {
            debug!(
                "process_registered_region_obligations: sup_type={:?} sub_region={:?} origin={:?}",
                sup_type, sub_region, origin
            );

            let sup_type = self.resolve_vars_if_possible(sup_type);

            let outlives =
                &mut TypeOutlives::new(self, self.tcx, &region_bound_pairs, None, param_env);
            let category = origin.to_constraint_category();
            outlives.type_must_outlive(origin, sup_type, sub_region, category);
        }
    }

    /// Processes registered region obliations and resolves regions, reporting
    /// any errors if any were raised. Prefer using this function over manually
    /// calling `resolve_regions_and_report_errors`.
    pub fn check_region_obligations_and_report_errors(
        &self,
        generic_param_scope: LocalDefId,
        outlives_env: &OutlivesEnvironment<'tcx>,
    ) {
        self.process_registered_region_obligations(
            outlives_env.region_bound_pairs(),
            outlives_env.param_env,
        );

        self.err_ctxt().resolve_regions_and_report_errors(generic_param_scope, outlives_env)
    }
}

/// The `TypeOutlives` struct has the job of "lowering" a `T: 'a`
/// obligation into a series of `'a: 'b` constraints and "verify"s, as
/// described on the module comment. The final constraints are emitted
/// via a "delegate" of type `D` -- this is usually the `infcx`, which
/// accrues them into the `region_obligations` code, but for NLL we
/// use something else.
pub struct TypeOutlives<'cx, 'tcx, D>
where
    D: TypeOutlivesDelegate<'tcx>,
{
    // See the comments on `process_registered_region_obligations` for the meaning
    // of these fields.
    delegate: D,
    tcx: TyCtxt<'tcx>,
    verify_bound: VerifyBoundCx<'cx, 'tcx>,
}

pub trait TypeOutlivesDelegate<'tcx> {
    fn push_sub_region_constraint(
        &mut self,
        origin: SubregionOrigin<'tcx>,
        a: ty::Region<'tcx>,
        b: ty::Region<'tcx>,
        constraint_category: ConstraintCategory<'tcx>,
    );

    fn push_verify(
        &mut self,
        origin: SubregionOrigin<'tcx>,
        kind: GenericKind<'tcx>,
        a: ty::Region<'tcx>,
        bound: VerifyBound<'tcx>,
    );
}

impl<'cx, 'tcx, D> TypeOutlives<'cx, 'tcx, D>
where
    D: TypeOutlivesDelegate<'tcx>,
{
    pub fn new(
        delegate: D,
        tcx: TyCtxt<'tcx>,
        region_bound_pairs: &'cx RegionBoundPairs<'tcx>,
        implicit_region_bound: Option<ty::Region<'tcx>>,
        param_env: ty::ParamEnv<'tcx>,
    ) -> Self {
        Self {
            delegate,
            tcx,
            verify_bound: VerifyBoundCx::new(
                tcx,
                region_bound_pairs,
                implicit_region_bound,
                param_env,
            ),
        }
    }

    /// Adds constraints to inference such that `T: 'a` holds (or
    /// reports an error if it cannot).
    ///
    /// # Parameters
    ///
    /// - `origin`, the reason we need this constraint
    /// - `ty`, the type `T`
    /// - `region`, the region `'a`
    #[instrument(level = "debug", skip(self))]
    pub fn type_must_outlive(
        &mut self,
        origin: infer::SubregionOrigin<'tcx>,
        ty: Ty<'tcx>,
        region: ty::Region<'tcx>,
        category: ConstraintCategory<'tcx>,
    ) {
        assert!(!ty.has_escaping_bound_vars());

        let mut components = smallvec![];
        push_outlives_components(self.tcx, ty, &mut components);
        self.components_must_outlive(origin, &components, region, category);
    }

    fn components_must_outlive(
        &mut self,
        origin: infer::SubregionOrigin<'tcx>,
        components: &[Component<'tcx>],
        region: ty::Region<'tcx>,
        category: ConstraintCategory<'tcx>,
    ) {
        for component in components.iter() {
            let origin = origin.clone();
            match component {
                Component::Region(region1) => {
                    self.delegate.push_sub_region_constraint(origin, region, *region1, category);
                }
                Component::Param(param_ty) => {
                    self.param_ty_must_outlive(origin, region, *param_ty);
                }
                Component::Opaque(def_id, substs) => {
                    self.opaque_must_outlive(*def_id, substs, origin, region)
                }
                Component::Projection(projection_ty) => {
                    self.projection_must_outlive(origin, region, *projection_ty);
                }
                Component::EscapingProjection(subcomponents) => {
                    self.components_must_outlive(origin, &subcomponents, region, category);
                }
                Component::UnresolvedInferenceVariable(v) => {
                    // ignore this, we presume it will yield an error
                    // later, since if a type variable is not resolved by
                    // this point it never will be
                    self.tcx.sess.delay_span_bug(
                        origin.span(),
                        &format!("unresolved inference variable in outlives: {:?}", v),
                    );
                }
            }
        }
    }

    fn param_ty_must_outlive(
        &mut self,
        origin: infer::SubregionOrigin<'tcx>,
        region: ty::Region<'tcx>,
        param_ty: ty::ParamTy,
    ) {
        debug!(
            "param_ty_must_outlive(region={:?}, param_ty={:?}, origin={:?})",
            region, param_ty, origin
        );

        let generic = GenericKind::Param(param_ty);
        let verify_bound = self.verify_bound.param_bound(param_ty);
        self.delegate.push_verify(origin, generic, region, verify_bound);
    }

    #[instrument(level = "debug", skip(self))]
    fn opaque_must_outlive(
        &mut self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
        origin: infer::SubregionOrigin<'tcx>,
        region: ty::Region<'tcx>,
    ) {
        self.generic_must_outlive(
            origin,
            region,
            GenericKind::Opaque(def_id, substs),
            def_id,
            substs,
            true,
            |ty| match *ty.kind() {
                ty::Opaque(def_id, substs) => (def_id, substs),
                _ => bug!("expected only projection types from env, not {:?}", ty),
            },
        );
    }

    #[instrument(level = "debug", skip(self))]
    fn projection_must_outlive(
        &mut self,
        origin: infer::SubregionOrigin<'tcx>,
        region: ty::Region<'tcx>,
        projection_ty: ty::ProjectionTy<'tcx>,
    ) {
        self.generic_must_outlive(
            origin,
            region,
            GenericKind::Projection(projection_ty),
            projection_ty.item_def_id,
            projection_ty.substs,
            false,
            |ty| match ty.kind() {
                ty::Projection(projection_ty) => (projection_ty.item_def_id, projection_ty.substs),
                _ => bug!("expected only projection types from env, not {:?}", ty),
            },
        );
    }

    #[instrument(level = "debug", skip(self, filter))]
    fn generic_must_outlive(
        &mut self,
        origin: infer::SubregionOrigin<'tcx>,
        region: ty::Region<'tcx>,
        generic: GenericKind<'tcx>,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
        is_opaque: bool,
        filter: impl Fn(Ty<'tcx>) -> (DefId, SubstsRef<'tcx>),
    ) {
        // An optimization for a common case with opaque types.
        if substs.is_empty() {
            return;
        }

        // This case is thorny for inference. The fundamental problem is
        // that there are many cases where we have choice, and inference
        // doesn't like choice (the current region inference in
        // particular). :) First off, we have to choose between using the
        // OutlivesProjectionEnv, OutlivesProjectionTraitDef, and
        // OutlivesProjectionComponent rules, any one of which is
        // sufficient.  If there are no inference variables involved, it's
        // not hard to pick the right rule, but if there are, we're in a
        // bit of a catch 22: if we picked which rule we were going to
        // use, we could add constraints to the region inference graph
        // that make it apply, but if we don't add those constraints, the
        // rule might not apply (but another rule might). For now, we err
        // on the side of adding too few edges into the graph.

        // Compute the bounds we can derive from the trait definition.
        // These are guaranteed to apply, no matter the inference
        // results.
        let trait_bounds: Vec<_> =
            self.verify_bound.declared_region_bounds(def_id, substs).collect();

        debug!(?trait_bounds);

        // Compute the bounds we can derive from the environment. This
        // is an "approximate" match -- in some cases, these bounds
        // may not apply.
        let mut approx_env_bounds = self.verify_bound.approx_declared_bounds_from_env(generic);
        debug!(?approx_env_bounds);

        // Remove outlives bounds that we get from the environment but
        // which are also deducible from the trait. This arises (cc
        // #55756) in cases where you have e.g., `<T as Foo<'a>>::Item:
        // 'a` in the environment but `trait Foo<'b> { type Item: 'b
        // }` in the trait definition.
        approx_env_bounds.retain(|bound_outlives| {
            // OK to skip binder because we only manipulate and compare against other
            // values from the same binder. e.g. if we have (e.g.) `for<'a> <T as Trait<'a>>::Item: 'a`
            // in `bound`, the `'a` will be a `^1` (bound, debruijn index == innermost) region.
            // If the declaration is `trait Trait<'b> { type Item: 'b; }`, then `projection_declared_bounds_from_trait`
            // will be invoked with `['b => ^1]` and so we will get `^1` returned.
            let bound = bound_outlives.skip_binder();
            let (def_id, substs) = filter(bound.0);
            self.verify_bound.declared_region_bounds(def_id, substs).all(|r| r != bound.1)
        });

        // If declared bounds list is empty, the only applicable rule is
        // OutlivesProjectionComponent. If there are inference variables,
        // then, we can break down the outlives into more primitive
        // components without adding unnecessary edges.
        //
        // If there are *no* inference variables, however, we COULD do
        // this, but we choose not to, because the error messages are less
        // good. For example, a requirement like `T::Item: 'r` would be
        // translated to a requirement that `T: 'r`; when this is reported
        // to the user, it will thus say "T: 'r must hold so that T::Item:
        // 'r holds". But that makes it sound like the only way to fix
        // the problem is to add `T: 'r`, which isn't true. So, if there are no
        // inference variables, we use a verify constraint instead of adding
        // edges, which winds up enforcing the same condition.
        let needs_infer = substs.needs_infer();
        if approx_env_bounds.is_empty() && trait_bounds.is_empty() && (needs_infer || is_opaque) {
            debug!("no declared bounds");

            self.substs_must_outlive(substs, origin, region);

            return;
        }

        // If we found a unique bound `'b` from the trait, and we
        // found nothing else from the environment, then the best
        // action is to require that `'b: 'r`, so do that.
        //
        // This is best no matter what rule we use:
        //
        // - OutlivesProjectionEnv: these would translate to the requirement that `'b:'r`
        // - OutlivesProjectionTraitDef: these would translate to the requirement that `'b:'r`
        // - OutlivesProjectionComponent: this would require `'b:'r`
        //   in addition to other conditions
        if !trait_bounds.is_empty()
            && trait_bounds[1..]
                .iter()
                .map(|r| Some(*r))
                .chain(
                    // NB: The environment may contain `for<'a> T: 'a` style bounds.
                    // In that case, we don't know if they are equal to the trait bound
                    // or not (since we don't *know* whether the environment bound even applies),
                    // so just map to `None` here if there are bound vars, ensuring that
                    // the call to `all` will fail below.
                    approx_env_bounds.iter().map(|b| b.map_bound(|b| b.1).no_bound_vars()),
                )
                .all(|b| b == Some(trait_bounds[0]))
        {
            let unique_bound = trait_bounds[0];
            debug!(?unique_bound);
            debug!("unique declared bound appears in trait ref");
            let category = origin.to_constraint_category();
            self.delegate.push_sub_region_constraint(origin, region, unique_bound, category);
            return;
        }

        // Fallback to verifying after the fact that there exists a
        // declared bound, or that all the components appearing in the
        // projection outlive; in some cases, this may add insufficient
        // edges into the inference graph, leading to inference failures
        // even though a satisfactory solution exists.
        let verify_bound = self.verify_bound.projection_opaque_bounds(
            generic,
            def_id,
            substs,
            &mut Default::default(),
        );
        debug!("projection_must_outlive: pushing {:?}", verify_bound);
        self.delegate.push_verify(origin, generic, region, verify_bound);
    }

    fn substs_must_outlive(
        &mut self,
        substs: SubstsRef<'tcx>,
        origin: infer::SubregionOrigin<'tcx>,
        region: ty::Region<'tcx>,
    ) {
        let constraint = origin.to_constraint_category();
        for k in substs {
            match k.unpack() {
                GenericArgKind::Lifetime(lt) => {
                    self.delegate.push_sub_region_constraint(
                        origin.clone(),
                        region,
                        lt,
                        constraint,
                    );
                }
                GenericArgKind::Type(ty) => {
                    self.type_must_outlive(origin.clone(), ty, region, constraint);
                }
                GenericArgKind::Const(_) => {
                    // Const parameters don't impose constraints.
                }
            }
        }
    }
}

impl<'cx, 'tcx> TypeOutlivesDelegate<'tcx> for &'cx InferCtxt<'tcx> {
    fn push_sub_region_constraint(
        &mut self,
        origin: SubregionOrigin<'tcx>,
        a: ty::Region<'tcx>,
        b: ty::Region<'tcx>,
        _constraint_category: ConstraintCategory<'tcx>,
    ) {
        self.sub_regions(origin, a, b)
    }

    fn push_verify(
        &mut self,
        origin: SubregionOrigin<'tcx>,
        kind: GenericKind<'tcx>,
        a: ty::Region<'tcx>,
        bound: VerifyBound<'tcx>,
    ) {
        self.verify_generic_bound(origin, kind, a, bound)
    }
}
