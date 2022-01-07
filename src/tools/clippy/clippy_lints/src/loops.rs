use crate::consts::constant;
use crate::reexport::Name;
use crate::utils::paths;
use crate::utils::usage::{is_unused, mutated_variables};
use crate::utils::{
    get_enclosing_block, get_parent_expr, get_trait_def_id, has_iter_method, higher, implements_trait,
    is_integer_const, is_no_std_crate, is_refutable, last_path_segment, match_trait_method, match_type, match_var,
    multispan_sugg, snippet, snippet_opt, snippet_with_applicability, span_lint, span_lint_and_help,
    span_lint_and_sugg, span_lint_and_then, SpanlessEq,
};
use crate::utils::{is_type_diagnostic_item, qpath_res, sugg};
use if_chain::if_chain;
use rustc_ast::ast;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_errors::Applicability;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::intravisit::{walk_block, walk_expr, walk_pat, walk_stmt, NestedVisitorMap, Visitor};
use rustc_hir::{
    def_id, BinOpKind, BindingAnnotation, Block, BorrowKind, Expr, ExprKind, GenericArg, HirId, InlineAsmOperand,
    LoopSource, MatchSource, Mutability, Node, Pat, PatKind, QPath, Stmt, StmtKind,
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::hir::map::Map;
use rustc_middle::lint::in_external_macro;
use rustc_middle::middle::region;
use rustc_middle::ty::{self, Ty, TyS};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::source_map::Span;
use rustc_span::symbol::Symbol;
use rustc_typeck::expr_use_visitor::{ConsumeMode, Delegate, ExprUseVisitor, PlaceBase, PlaceWithHirId};
use std::iter::{once, Iterator};
use std::mem;

declare_clippy_lint! {
    /// **What it does:** Checks for for-loops that manually copy items between
    /// slices that could be optimized by having a memcpy.
    ///
    /// **Why is this bad?** It is not as fast as a memcpy.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    /// ```rust
    /// # let src = vec![1];
    /// # let mut dst = vec![0; 65];
    /// for i in 0..src.len() {
    ///     dst[i + 64] = src[i];
    /// }
    /// ```
    /// Could be written as:
    /// ```rust
    /// # let src = vec![1];
    /// # let mut dst = vec![0; 65];
    /// dst[64..(src.len() + 64)].clone_from_slice(&src[..]);
    /// ```
    pub MANUAL_MEMCPY,
    perf,
    "manually copying items between slices"
}

declare_clippy_lint! {
    /// **What it does:** Checks for looping over the range of `0..len` of some
    /// collection just to get the values by index.
    ///
    /// **Why is this bad?** Just iterating the collection itself makes the intent
    /// more clear and is probably faster.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    /// ```rust
    /// let vec = vec!['a', 'b', 'c'];
    /// for i in 0..vec.len() {
    ///     println!("{}", vec[i]);
    /// }
    /// ```
    /// Could be written as:
    /// ```rust
    /// let vec = vec!['a', 'b', 'c'];
    /// for i in vec {
    ///     println!("{}", i);
    /// }
    /// ```
    pub NEEDLESS_RANGE_LOOP,
    style,
    "for-looping over a range of indices where an iterator over items would do"
}

declare_clippy_lint! {
    /// **What it does:** Checks for loops on `x.iter()` where `&x` will do, and
    /// suggests the latter.
    ///
    /// **Why is this bad?** Readability.
    ///
    /// **Known problems:** False negatives. We currently only warn on some known
    /// types.
    ///
    /// **Example:**
    /// ```rust
    /// // with `y` a `Vec` or slice:
    /// # let y = vec![1];
    /// for x in y.iter() {
    ///     // ..
    /// }
    /// ```
    /// can be rewritten to
    /// ```rust
    /// # let y = vec![1];
    /// for x in &y {
    ///     // ..
    /// }
    /// ```
    pub EXPLICIT_ITER_LOOP,
    pedantic,
    "for-looping over `_.iter()` or `_.iter_mut()` when `&_` or `&mut _` would do"
}

declare_clippy_lint! {
    /// **What it does:** Checks for loops on `y.into_iter()` where `y` will do, and
    /// suggests the latter.
    ///
    /// **Why is this bad?** Readability.
    ///
    /// **Known problems:** None
    ///
    /// **Example:**
    /// ```rust
    /// # let y = vec![1];
    /// // with `y` a `Vec` or slice:
    /// for x in y.into_iter() {
    ///     // ..
    /// }
    /// ```
    /// can be rewritten to
    /// ```rust
    /// # let y = vec![1];
    /// for x in y {
    ///     // ..
    /// }
    /// ```
    pub EXPLICIT_INTO_ITER_LOOP,
    pedantic,
    "for-looping over `_.into_iter()` when `_` would do"
}

declare_clippy_lint! {
    /// **What it does:** Checks for loops on `x.next()`.
    ///
    /// **Why is this bad?** `next()` returns either `Some(value)` if there was a
    /// value, or `None` otherwise. The insidious thing is that `Option<_>`
    /// implements `IntoIterator`, so that possibly one value will be iterated,
    /// leading to some hard to find bugs. No one will want to write such code
    /// [except to win an Underhanded Rust
    /// Contest](https://www.reddit.com/r/rust/comments/3hb0wm/underhanded_rust_contest/cu5yuhr).
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    /// ```ignore
    /// for x in y.next() {
    ///     ..
    /// }
    /// ```
    pub ITER_NEXT_LOOP,
    correctness,
    "for-looping over `_.next()` which is probably not intended"
}

declare_clippy_lint! {
    /// **What it does:** Checks for `for` loops over `Option` or `Result` values.
    ///
    /// **Why is this bad?** Readability. This is more clearly expressed as an `if
    /// let`.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    /// ```rust
    /// # let opt = Some(1);
    ///
    /// // Bad
    /// for x in opt {
    ///     // ..
    /// }
    ///
    /// // Good
    /// if let Some(x) = opt {
    ///     // ..
    /// }
    /// ```
    ///
    /// // or
    ///
    /// ```rust
    /// # let res: Result<i32, std::io::Error> = Ok(1);
    ///
    /// // Bad
    /// for x in &res {
    ///     // ..
    /// }
    ///
    /// // Good
    /// if let Ok(x) = res {
    ///     // ..
    /// }
    /// ```
    pub FOR_LOOPS_OVER_FALLIBLES,
    correctness,
    "for-looping over an `Option` or a `Result`, which is more clearly expressed as an `if let`"
}

declare_clippy_lint! {
    /// **What it does:** Detects `loop + match` combinations that are easier
    /// written as a `while let` loop.
    ///
    /// **Why is this bad?** The `while let` loop is usually shorter and more
    /// readable.
    ///
    /// **Known problems:** Sometimes the wrong binding is displayed (#383).
    ///
    /// **Example:**
    /// ```rust,no_run
    /// # let y = Some(1);
    /// loop {
    ///     let x = match y {
    ///         Some(x) => x,
    ///         None => break,
    ///     };
    ///     // .. do something with x
    /// }
    /// // is easier written as
    /// while let Some(x) = y {
    ///     // .. do something with x
    /// };
    /// ```
    pub WHILE_LET_LOOP,
    complexity,
    "`loop { if let { ... } else break }`, which can be written as a `while let` loop"
}

declare_clippy_lint! {
    /// **What it does:** Checks for functions collecting an iterator when collect
    /// is not needed.
    ///
    /// **Why is this bad?** `collect` causes the allocation of a new data structure,
    /// when this allocation may not be needed.
    ///
    /// **Known problems:**
    /// None
    ///
    /// **Example:**
    /// ```rust
    /// # let iterator = vec![1].into_iter();
    /// let len = iterator.clone().collect::<Vec<_>>().len();
    /// // should be
    /// let len = iterator.count();
    /// ```
    pub NEEDLESS_COLLECT,
    perf,
    "collecting an iterator when collect is not needed"
}

declare_clippy_lint! {
    /// **What it does:** Checks `for` loops over slices with an explicit counter
    /// and suggests the use of `.enumerate()`.
    ///
    /// **Why is it bad?** Using `.enumerate()` makes the intent more clear,
    /// declutters the code and may be faster in some instances.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    /// ```rust
    /// # let v = vec![1];
    /// # fn bar(bar: usize, baz: usize) {}
    /// let mut i = 0;
    /// for item in &v {
    ///     bar(i, *item);
    ///     i += 1;
    /// }
    /// ```
    /// Could be written as
    /// ```rust
    /// # let v = vec![1];
    /// # fn bar(bar: usize, baz: usize) {}
    /// for (i, item) in v.iter().enumerate() { bar(i, *item); }
    /// ```
    pub EXPLICIT_COUNTER_LOOP,
    complexity,
    "for-looping with an explicit counter when `_.enumerate()` would do"
}

declare_clippy_lint! {
    /// **What it does:** Checks for empty `loop` expressions.
    ///
    /// **Why is this bad?** Those busy loops burn CPU cycles without doing
    /// anything. Think of the environment and either block on something or at least
    /// make the thread sleep for some microseconds.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    /// ```no_run
    /// loop {}
    /// ```
    pub EMPTY_LOOP,
    style,
    "empty `loop {}`, which should block or sleep"
}

declare_clippy_lint! {
    /// **What it does:** Checks for `while let` expressions on iterators.
    ///
    /// **Why is this bad?** Readability. A simple `for` loop is shorter and conveys
    /// the intent better.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    /// ```ignore
    /// while let Some(val) = iter() {
    ///     ..
    /// }
    /// ```
    pub WHILE_LET_ON_ITERATOR,
    style,
    "using a while-let loop instead of a for loop on an iterator"
}

declare_clippy_lint! {
    /// **What it does:** Checks for iterating a map (`HashMap` or `BTreeMap`) and
    /// ignoring either the keys or values.
    ///
    /// **Why is this bad?** Readability. There are `keys` and `values` methods that
    /// can be used to express that don't need the values or keys.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    /// ```ignore
    /// for (k, _) in &map {
    ///     ..
    /// }
    /// ```
    ///
    /// could be replaced by
    ///
    /// ```ignore
    /// for k in map.keys() {
    ///     ..
    /// }
    /// ```
    pub FOR_KV_MAP,
    style,
    "looping on a map using `iter` when `keys` or `values` would do"
}

declare_clippy_lint! {
    /// **What it does:** Checks for loops that will always `break`, `return` or
    /// `continue` an outer loop.
    ///
    /// **Why is this bad?** This loop never loops, all it does is obfuscating the
    /// code.
    ///
    /// **Known problems:** None
    ///
    /// **Example:**
    /// ```rust
    /// loop {
    ///     ..;
    ///     break;
    /// }
    /// ```
    pub NEVER_LOOP,
    correctness,
    "any loop that will always `break` or `return`"
}

declare_clippy_lint! {
    /// **What it does:** Checks for loops which have a range bound that is a mutable variable
    ///
    /// **Why is this bad?** One might think that modifying the mutable variable changes the loop bounds
    ///
    /// **Known problems:** None
    ///
    /// **Example:**
    /// ```rust
    /// let mut foo = 42;
    /// for i in 0..foo {
    ///     foo -= 1;
    ///     println!("{}", i); // prints numbers from 0 to 42, not 0 to 21
    /// }
    /// ```
    pub MUT_RANGE_BOUND,
    complexity,
    "for loop over a range where one of the bounds is a mutable variable"
}

declare_clippy_lint! {
    /// **What it does:** Checks whether variables used within while loop condition
    /// can be (and are) mutated in the body.
    ///
    /// **Why is this bad?** If the condition is unchanged, entering the body of the loop
    /// will lead to an infinite loop.
    ///
    /// **Known problems:** If the `while`-loop is in a closure, the check for mutation of the
    /// condition variables in the body can cause false negatives. For example when only `Upvar` `a` is
    /// in the condition and only `Upvar` `b` gets mutated in the body, the lint will not trigger.
    ///
    /// **Example:**
    /// ```rust
    /// let i = 0;
    /// while i > 10 {
    ///     println!("let me loop forever!");
    /// }
    /// ```
    pub WHILE_IMMUTABLE_CONDITION,
    correctness,
    "variables used within while expression are not mutated in the body"
}

declare_lint_pass!(Loops => [
    MANUAL_MEMCPY,
    NEEDLESS_RANGE_LOOP,
    EXPLICIT_ITER_LOOP,
    EXPLICIT_INTO_ITER_LOOP,
    ITER_NEXT_LOOP,
    FOR_LOOPS_OVER_FALLIBLES,
    WHILE_LET_LOOP,
    NEEDLESS_COLLECT,
    EXPLICIT_COUNTER_LOOP,
    EMPTY_LOOP,
    WHILE_LET_ON_ITERATOR,
    FOR_KV_MAP,
    NEVER_LOOP,
    MUT_RANGE_BOUND,
    WHILE_IMMUTABLE_CONDITION,
]);

impl<'tcx> LateLintPass<'tcx> for Loops {
    #[allow(clippy::too_many_lines)]
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'_>) {
        if let Some((pat, arg, body)) = higher::for_loop(expr) {
            // we don't want to check expanded macros
            // this check is not at the top of the function
            // since higher::for_loop expressions are marked as expansions
            if body.span.from_expansion() {
                return;
            }
            check_for_loop(cx, pat, arg, body, expr);
        }

        // we don't want to check expanded macros
        if expr.span.from_expansion() {
            return;
        }

        // check for never_loop
        if let ExprKind::Loop(ref block, _, _) = expr.kind {
            match never_loop_block(block, expr.hir_id) {
                NeverLoopResult::AlwaysBreak => span_lint(cx, NEVER_LOOP, expr.span, "this loop never actually loops"),
                NeverLoopResult::MayContinueMainLoop | NeverLoopResult::Otherwise => (),
            }
        }

        // check for `loop { if let {} else break }` that could be `while let`
        // (also matches an explicit "match" instead of "if let")
        // (even if the "match" or "if let" is used for declaration)
        if let ExprKind::Loop(ref block, _, LoopSource::Loop) = expr.kind {
            // also check for empty `loop {}` statements
            if block.stmts.is_empty() && block.expr.is_none() && !is_no_std_crate(cx.tcx.hir().krate()) {
                span_lint(
                    cx,
                    EMPTY_LOOP,
                    expr.span,
                    "empty `loop {}` detected. You may want to either use `panic!()` or add \
                     `std::thread::sleep(..);` to the loop body.",
                );
            }

            // extract the expression from the first statement (if any) in a block
            let inner_stmt_expr = extract_expr_from_first_stmt(block);
            // or extract the first expression (if any) from the block
            if let Some(inner) = inner_stmt_expr.or_else(|| extract_first_expr(block)) {
                if let ExprKind::Match(ref matchexpr, ref arms, ref source) = inner.kind {
                    // ensure "if let" compatible match structure
                    match *source {
                        MatchSource::Normal | MatchSource::IfLetDesugar { .. } => {
                            if arms.len() == 2
                                && arms[0].guard.is_none()
                                && arms[1].guard.is_none()
                                && is_simple_break_expr(&arms[1].body)
                            {
                                if in_external_macro(cx.sess(), expr.span) {
                                    return;
                                }

                                // NOTE: we used to build a body here instead of using
                                // ellipsis, this was removed because:
                                // 1) it was ugly with big bodies;
                                // 2) it was not indented properly;
                                // 3) it wasn’t very smart (see #675).
                                let mut applicability = Applicability::HasPlaceholders;
                                span_lint_and_sugg(
                                    cx,
                                    WHILE_LET_LOOP,
                                    expr.span,
                                    "this loop could be written as a `while let` loop",
                                    "try",
                                    format!(
                                        "while let {} = {} {{ .. }}",
                                        snippet_with_applicability(cx, arms[0].pat.span, "..", &mut applicability),
                                        snippet_with_applicability(cx, matchexpr.span, "..", &mut applicability),
                                    ),
                                    applicability,
                                );
                            }
                        },
                        _ => (),
                    }
                }
            }
        }
        if let ExprKind::Match(ref match_expr, ref arms, MatchSource::WhileLetDesugar) = expr.kind {
            let pat = &arms[0].pat.kind;
            if let (
                &PatKind::TupleStruct(ref qpath, ref pat_args, _),
                &ExprKind::MethodCall(ref method_path, _, ref method_args, _),
            ) = (pat, &match_expr.kind)
            {
                let iter_expr = &method_args[0];

                // Don't lint when the iterator is recreated on every iteration
                if_chain! {
                    if let ExprKind::MethodCall(..) | ExprKind::Call(..) = iter_expr.kind;
                    if let Some(iter_def_id) = get_trait_def_id(cx, &paths::ITERATOR);
                    if implements_trait(cx, cx.tables().expr_ty(iter_expr), iter_def_id, &[]);
                    then {
                        return;
                    }
                }

                let lhs_constructor = last_path_segment(qpath);
                if method_path.ident.name == sym!(next)
                    && match_trait_method(cx, match_expr, &paths::ITERATOR)
                    && lhs_constructor.ident.name == sym!(Some)
                    && (pat_args.is_empty()
                        || !is_refutable(cx, &pat_args[0])
                            && !is_used_inside(cx, iter_expr, &arms[0].body)
                            && !is_iterator_used_after_while_let(cx, iter_expr)
                            && !is_nested(cx, expr, &method_args[0]))
                {
                    let mut applicability = Applicability::MachineApplicable;
                    let iterator = snippet_with_applicability(cx, method_args[0].span, "_", &mut applicability);
                    let loop_var = if pat_args.is_empty() {
                        "_".to_string()
                    } else {
                        snippet_with_applicability(cx, pat_args[0].span, "_", &mut applicability).into_owned()
                    };
                    span_lint_and_sugg(
                        cx,
                        WHILE_LET_ON_ITERATOR,
                        expr.span.with_hi(match_expr.span.hi()),
                        "this loop could be written as a `for` loop",
                        "try",
                        format!("for {} in {}", loop_var, iterator),
                        applicability,
                    );
                }
            }
        }

        if let Some((cond, body)) = higher::while_loop(&expr) {
            check_infinite_loop(cx, cond, body);
        }

        check_needless_collect(expr, cx);
    }
}

enum NeverLoopResult {
    // A break/return always get triggered but not necessarily for the main loop.
    AlwaysBreak,
    // A continue may occur for the main loop.
    MayContinueMainLoop,
    Otherwise,
}

#[must_use]
fn absorb_break(arg: &NeverLoopResult) -> NeverLoopResult {
    match *arg {
        NeverLoopResult::AlwaysBreak | NeverLoopResult::Otherwise => NeverLoopResult::Otherwise,
        NeverLoopResult::MayContinueMainLoop => NeverLoopResult::MayContinueMainLoop,
    }
}

// Combine two results for parts that are called in order.
#[must_use]
fn combine_seq(first: NeverLoopResult, second: NeverLoopResult) -> NeverLoopResult {
    match first {
        NeverLoopResult::AlwaysBreak | NeverLoopResult::MayContinueMainLoop => first,
        NeverLoopResult::Otherwise => second,
    }
}

// Combine two results where both parts are called but not necessarily in order.
#[must_use]
fn combine_both(left: NeverLoopResult, right: NeverLoopResult) -> NeverLoopResult {
    match (left, right) {
        (NeverLoopResult::MayContinueMainLoop, _) | (_, NeverLoopResult::MayContinueMainLoop) => {
            NeverLoopResult::MayContinueMainLoop
        },
        (NeverLoopResult::AlwaysBreak, _) | (_, NeverLoopResult::AlwaysBreak) => NeverLoopResult::AlwaysBreak,
        (NeverLoopResult::Otherwise, NeverLoopResult::Otherwise) => NeverLoopResult::Otherwise,
    }
}

// Combine two results where only one of the part may have been executed.
#[must_use]
fn combine_branches(b1: NeverLoopResult, b2: NeverLoopResult) -> NeverLoopResult {
    match (b1, b2) {
        (NeverLoopResult::AlwaysBreak, NeverLoopResult::AlwaysBreak) => NeverLoopResult::AlwaysBreak,
        (NeverLoopResult::MayContinueMainLoop, _) | (_, NeverLoopResult::MayContinueMainLoop) => {
            NeverLoopResult::MayContinueMainLoop
        },
        (NeverLoopResult::Otherwise, _) | (_, NeverLoopResult::Otherwise) => NeverLoopResult::Otherwise,
    }
}

fn never_loop_block(block: &Block<'_>, main_loop_id: HirId) -> NeverLoopResult {
    let stmts = block.stmts.iter().map(stmt_to_expr);
    let expr = once(block.expr.as_deref());
    let mut iter = stmts.chain(expr).filter_map(|e| e);
    never_loop_expr_seq(&mut iter, main_loop_id)
}

fn stmt_to_expr<'tcx>(stmt: &Stmt<'tcx>) -> Option<&'tcx Expr<'tcx>> {
    match stmt.kind {
        StmtKind::Semi(ref e, ..) | StmtKind::Expr(ref e, ..) => Some(e),
        StmtKind::Local(ref local) => local.init.as_deref(),
        _ => None,
    }
}

fn never_loop_expr(expr: &Expr<'_>, main_loop_id: HirId) -> NeverLoopResult {
    match expr.kind {
        ExprKind::Box(ref e)
        | ExprKind::Unary(_, ref e)
        | ExprKind::Cast(ref e, _)
        | ExprKind::Type(ref e, _)
        | ExprKind::Field(ref e, _)
        | ExprKind::AddrOf(_, _, ref e)
        | ExprKind::Struct(_, _, Some(ref e))
        | ExprKind::Repeat(ref e, _)
        | ExprKind::DropTemps(ref e) => never_loop_expr(e, main_loop_id),
        ExprKind::Array(ref es) | ExprKind::MethodCall(_, _, ref es, _) | ExprKind::Tup(ref es) => {
            never_loop_expr_all(&mut es.iter(), main_loop_id)
        },
        ExprKind::Call(ref e, ref es) => never_loop_expr_all(&mut once(&**e).chain(es.iter()), main_loop_id),
        ExprKind::Binary(_, ref e1, ref e2)
        | ExprKind::Assign(ref e1, ref e2, _)
        | ExprKind::AssignOp(_, ref e1, ref e2)
        | ExprKind::Index(ref e1, ref e2) => never_loop_expr_all(&mut [&**e1, &**e2].iter().cloned(), main_loop_id),
        ExprKind::Loop(ref b, _, _) => {
            // Break can come from the inner loop so remove them.
            absorb_break(&never_loop_block(b, main_loop_id))
        },
        ExprKind::Match(ref e, ref arms, _) => {
            let e = never_loop_expr(e, main_loop_id);
            if arms.is_empty() {
                e
            } else {
                let arms = never_loop_expr_branch(&mut arms.iter().map(|a| &*a.body), main_loop_id);
                combine_seq(e, arms)
            }
        },
        ExprKind::Block(ref b, _) => never_loop_block(b, main_loop_id),
        ExprKind::Continue(d) => {
            let id = d
                .target_id
                .expect("target ID can only be missing in the presence of compilation errors");
            if id == main_loop_id {
                NeverLoopResult::MayContinueMainLoop
            } else {
                NeverLoopResult::AlwaysBreak
            }
        },
        ExprKind::Break(_, ref e) | ExprKind::Ret(ref e) => {
            if let Some(ref e) = *e {
                combine_seq(never_loop_expr(e, main_loop_id), NeverLoopResult::AlwaysBreak)
            } else {
                NeverLoopResult::AlwaysBreak
            }
        },
        ExprKind::InlineAsm(ref asm) => asm
            .operands
            .iter()
            .map(|o| match o {
                InlineAsmOperand::In { expr, .. }
                | InlineAsmOperand::InOut { expr, .. }
                | InlineAsmOperand::Const { expr }
                | InlineAsmOperand::Sym { expr } => never_loop_expr(expr, main_loop_id),
                InlineAsmOperand::Out { expr, .. } => never_loop_expr_all(&mut expr.iter(), main_loop_id),
                InlineAsmOperand::SplitInOut { in_expr, out_expr, .. } => {
                    never_loop_expr_all(&mut once(in_expr).chain(out_expr.iter()), main_loop_id)
                },
            })
            .fold(NeverLoopResult::Otherwise, combine_both),
        ExprKind::Struct(_, _, None)
        | ExprKind::Yield(_, _)
        | ExprKind::Closure(_, _, _, _, _)
        | ExprKind::LlvmInlineAsm(_)
        | ExprKind::Path(_)
        | ExprKind::Lit(_)
        | ExprKind::Err => NeverLoopResult::Otherwise,
    }
}

fn never_loop_expr_seq<'a, T: Iterator<Item = &'a Expr<'a>>>(es: &mut T, main_loop_id: HirId) -> NeverLoopResult {
    es.map(|e| never_loop_expr(e, main_loop_id))
        .fold(NeverLoopResult::Otherwise, combine_seq)
}

fn never_loop_expr_all<'a, T: Iterator<Item = &'a Expr<'a>>>(es: &mut T, main_loop_id: HirId) -> NeverLoopResult {
    es.map(|e| never_loop_expr(e, main_loop_id))
        .fold(NeverLoopResult::Otherwise, combine_both)
}

fn never_loop_expr_branch<'a, T: Iterator<Item = &'a Expr<'a>>>(e: &mut T, main_loop_id: HirId) -> NeverLoopResult {
    e.map(|e| never_loop_expr(e, main_loop_id))
        .fold(NeverLoopResult::AlwaysBreak, combine_branches)
}

fn check_for_loop<'tcx>(
    cx: &LateContext<'tcx>,
    pat: &'tcx Pat<'_>,
    arg: &'tcx Expr<'_>,
    body: &'tcx Expr<'_>,
    expr: &'tcx Expr<'_>,
) {
    check_for_loop_range(cx, pat, arg, body, expr);
    check_for_loop_arg(cx, pat, arg, expr);
    check_for_loop_explicit_counter(cx, pat, arg, body, expr);
    check_for_loop_over_map_kv(cx, pat, arg, body, expr);
    check_for_mut_range_bound(cx, arg, body);
    detect_manual_memcpy(cx, pat, arg, body, expr);
}

fn same_var<'tcx>(cx: &LateContext<'tcx>, expr: &Expr<'_>, var: HirId) -> bool {
    if_chain! {
        if let ExprKind::Path(qpath) = &expr.kind;
        if let QPath::Resolved(None, path) = qpath;
        if path.segments.len() == 1;
        if let Res::Local(local_id) = qpath_res(cx, qpath, expr.hir_id);
        then {
            // our variable!
            local_id == var
        } else {
            false
        }
    }
}

#[derive(Clone, Copy)]
enum OffsetSign {
    Positive,
    Negative,
}

struct Offset {
    value: String,
    sign: OffsetSign,
}

impl Offset {
    fn negative(value: String) -> Self {
        Self {
            value,
            sign: OffsetSign::Negative,
        }
    }

    fn positive(value: String) -> Self {
        Self {
            value,
            sign: OffsetSign::Positive,
        }
    }
}

struct FixedOffsetVar<'hir> {
    var: &'hir Expr<'hir>,
    offset: Offset,
}

fn is_slice_like<'tcx>(cx: &LateContext<'tcx>, ty: Ty<'_>) -> bool {
    let is_slice = match ty.kind {
        ty::Ref(_, subty, _) => is_slice_like(cx, subty),
        ty::Slice(..) | ty::Array(..) => true,
        _ => false,
    };

    is_slice || is_type_diagnostic_item(cx, ty, sym!(vec_type)) || is_type_diagnostic_item(cx, ty, sym!(vecdeque_type))
}

fn fetch_cloned_expr<'tcx>(expr: &'tcx Expr<'tcx>) -> &'tcx Expr<'tcx> {
    if_chain! {
        if let ExprKind::MethodCall(method, _, args, _) = expr.kind;
        if method.ident.name == sym!(clone);
        if args.len() == 1;
        if let Some(arg) = args.get(0);
        then { arg } else { expr }
    }
}

fn get_offset<'tcx>(cx: &LateContext<'tcx>, idx: &Expr<'_>, var: HirId) -> Option<Offset> {
    fn extract_offset<'tcx>(cx: &LateContext<'tcx>, e: &Expr<'_>, var: HirId) -> Option<String> {
        match &e.kind {
            ExprKind::Lit(l) => match l.node {
                ast::LitKind::Int(x, _ty) => Some(x.to_string()),
                _ => None,
            },
            ExprKind::Path(..) if !same_var(cx, e, var) => Some(snippet_opt(cx, e.span).unwrap_or_else(|| "??".into())),
            _ => None,
        }
    }

    match idx.kind {
        ExprKind::Binary(op, lhs, rhs) => match op.node {
            BinOpKind::Add => {
                let offset_opt = if same_var(cx, lhs, var) {
                    extract_offset(cx, rhs, var)
                } else if same_var(cx, rhs, var) {
                    extract_offset(cx, lhs, var)
                } else {
                    None
                };

                offset_opt.map(Offset::positive)
            },
            BinOpKind::Sub if same_var(cx, lhs, var) => extract_offset(cx, rhs, var).map(Offset::negative),
            _ => None,
        },
        ExprKind::Path(..) if same_var(cx, idx, var) => Some(Offset::positive("0".into())),
        _ => None,
    }
}

fn get_assignments<'tcx>(body: &'tcx Expr<'tcx>) -> impl Iterator<Item = Option<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>)>> {
    fn get_assignment<'tcx>(e: &'tcx Expr<'tcx>) -> Option<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>)> {
        if let ExprKind::Assign(lhs, rhs, _) = e.kind {
            Some((lhs, rhs))
        } else {
            None
        }
    }

    // This is one of few ways to return different iterators
    // derived from: https://stackoverflow.com/questions/29760668/conditionally-iterate-over-one-of-several-possible-iterators/52064434#52064434
    let mut iter_a = None;
    let mut iter_b = None;

    if let ExprKind::Block(b, _) = body.kind {
        let Block { stmts, expr, .. } = *b;

        iter_a = stmts
            .iter()
            .filter_map(|stmt| match stmt.kind {
                StmtKind::Local(..) | StmtKind::Item(..) => None,
                StmtKind::Expr(e) | StmtKind::Semi(e) => Some(e),
            })
            .chain(expr.into_iter())
            .map(get_assignment)
            .into()
    } else {
        iter_b = Some(get_assignment(body))
    }

    iter_a.into_iter().flatten().chain(iter_b.into_iter())
}

fn build_manual_memcpy_suggestion<'tcx>(
    cx: &LateContext<'tcx>,
    start: &Expr<'_>,
    end: &Expr<'_>,
    limits: ast::RangeLimits,
    dst_var: FixedOffsetVar<'_>,
    src_var: FixedOffsetVar<'_>,
) -> String {
    fn print_sum(arg1: &str, arg2: &Offset) -> String {
        match (arg1, &arg2.value[..], arg2.sign) {
            ("0", "0", _) => "0".into(),
            ("0", x, OffsetSign::Positive) | (x, "0", _) => x.into(),
            ("0", x, OffsetSign::Negative) => format!("-{}", x),
            (x, y, OffsetSign::Positive) => format!("({} + {})", x, y),
            (x, y, OffsetSign::Negative) => {
                if x == y {
                    "0".into()
                } else {
                    format!("({} - {})", x, y)
                }
            },
        }
    }

    fn print_offset(start_str: &str, inline_offset: &Offset) -> String {
        let offset = print_sum(start_str, inline_offset);
        if offset.as_str() == "0" {
            "".into()
        } else {
            offset
        }
    }

    let print_limit = |end: &Expr<'_>, offset: Offset, var: &Expr<'_>| {
        if_chain! {
            if let ExprKind::MethodCall(method, _, len_args, _) = end.kind;
            if method.ident.name == sym!(len);
            if len_args.len() == 1;
            if let Some(arg) = len_args.get(0);
            if var_def_id(cx, arg) == var_def_id(cx, var);
            then {
                match offset.sign {
                    OffsetSign::Negative => format!("({} - {})", snippet(cx, end.span, "<src>.len()"), offset.value),
                    OffsetSign::Positive => "".into(),
                }
            } else {
                let end_str = match limits {
                    ast::RangeLimits::Closed => {
                        let end = sugg::Sugg::hir(cx, end, "<count>");
                        format!("{}", end + sugg::ONE)
                    },
                    ast::RangeLimits::HalfOpen => format!("{}", snippet(cx, end.span, "..")),
                };

                print_sum(&end_str, &offset)
            }
        }
    };

    let start_str = snippet(cx, start.span, "").to_string();
    let dst_offset = print_offset(&start_str, &dst_var.offset);
    let dst_limit = print_limit(end, dst_var.offset, dst_var.var);
    let src_offset = print_offset(&start_str, &src_var.offset);
    let src_limit = print_limit(end, src_var.offset, src_var.var);

    let dst_var_name = snippet_opt(cx, dst_var.var.span).unwrap_or_else(|| "???".into());
    let src_var_name = snippet_opt(cx, src_var.var.span).unwrap_or_else(|| "???".into());

    let dst = if dst_offset == "" && dst_limit == "" {
        dst_var_name
    } else {
        format!("{}[{}..{}]", dst_var_name, dst_offset, dst_limit)
    };

    format!(
        "{}.clone_from_slice(&{}[{}..{}])",
        dst, src_var_name, src_offset, src_limit
    )
}
/// Checks for for loops that sequentially copy items from one slice-like
/// object to another.
fn detect_manual_memcpy<'tcx>(
    cx: &LateContext<'tcx>,
    pat: &'tcx Pat<'_>,
    arg: &'tcx Expr<'_>,
    body: &'tcx Expr<'_>,
    expr: &'tcx Expr<'_>,
) {
    if let Some(higher::Range {
        start: Some(start),
        end: Some(end),
        limits,
    }) = higher::range(cx, arg)
    {
        // the var must be a single name
        if let PatKind::Binding(_, canonical_id, _, _) = pat.kind {
            // The only statements in the for loops can be indexed assignments from
            // indexed retrievals.
            let big_sugg = get_assignments(body)
                .map(|o| {
                    o.and_then(|(lhs, rhs)| {
                        let rhs = fetch_cloned_expr(rhs);
                        if_chain! {
                            if let ExprKind::Index(seqexpr_left, idx_left) = lhs.kind;
                            if let ExprKind::Index(seqexpr_right, idx_right) = rhs.kind;
                            if is_slice_like(cx, cx.tables().expr_ty(seqexpr_left))
                                && is_slice_like(cx, cx.tables().expr_ty(seqexpr_right));
                            if let Some(offset_left) = get_offset(cx, &idx_left, canonical_id);
                            if let Some(offset_right) = get_offset(cx, &idx_right, canonical_id);

                            // Source and destination must be different
                            if var_def_id(cx, seqexpr_left) != var_def_id(cx, seqexpr_right);
                            then {
                                Some((FixedOffsetVar { var: seqexpr_left, offset: offset_left },
                                    FixedOffsetVar { var: seqexpr_right, offset: offset_right }))
                            } else {
                                None
                            }
                        }
                    })
                })
                .map(|o| o.map(|(dst, src)| build_manual_memcpy_suggestion(cx, start, end, limits, dst, src)))
                .collect::<Option<Vec<_>>>()
                .filter(|v| !v.is_empty())
                .map(|v| v.join("\n    "));

            if let Some(big_sugg) = big_sugg {
                span_lint_and_sugg(
                    cx,
                    MANUAL_MEMCPY,
                    expr.span,
                    "it looks like you're manually copying between slices",
                    "try replacing the loop by",
                    big_sugg,
                    Applicability::Unspecified,
                );
            }
        }
    }
}

/// Checks for looping over a range and then indexing a sequence with it.
/// The iteratee must be a range literal.
#[allow(clippy::too_many_lines)]
fn check_for_loop_range<'tcx>(
    cx: &LateContext<'tcx>,
    pat: &'tcx Pat<'_>,
    arg: &'tcx Expr<'_>,
    body: &'tcx Expr<'_>,
    expr: &'tcx Expr<'_>,
) {
    if let Some(higher::Range {
        start: Some(start),
        ref end,
        limits,
    }) = higher::range(cx, arg)
    {
        // the var must be a single name
        if let PatKind::Binding(_, canonical_id, ident, _) = pat.kind {
            let mut visitor = VarVisitor {
                cx,
                var: canonical_id,
                indexed_mut: FxHashSet::default(),
                indexed_indirectly: FxHashMap::default(),
                indexed_directly: FxHashMap::default(),
                referenced: FxHashSet::default(),
                nonindex: false,
                prefer_mutable: false,
            };
            walk_expr(&mut visitor, body);

            // linting condition: we only indexed one variable, and indexed it directly
            if visitor.indexed_indirectly.is_empty() && visitor.indexed_directly.len() == 1 {
                let (indexed, (indexed_extent, indexed_ty)) = visitor
                    .indexed_directly
                    .into_iter()
                    .next()
                    .expect("already checked that we have exactly 1 element");

                // ensure that the indexed variable was declared before the loop, see #601
                if let Some(indexed_extent) = indexed_extent {
                    let parent_id = cx.tcx.hir().get_parent_item(expr.hir_id);
                    let parent_def_id = cx.tcx.hir().local_def_id(parent_id);
                    let region_scope_tree = cx.tcx.region_scope_tree(parent_def_id);
                    let pat_extent = region_scope_tree.var_scope(pat.hir_id.local_id);
                    if region_scope_tree.is_subscope_of(indexed_extent, pat_extent) {
                        return;
                    }
                }

                // don't lint if the container that is indexed does not have .iter() method
                let has_iter = has_iter_method(cx, indexed_ty);
                if has_iter.is_none() {
                    return;
                }

                // don't lint if the container that is indexed into is also used without
                // indexing
                if visitor.referenced.contains(&indexed) {
                    return;
                }

                let starts_at_zero = is_integer_const(cx, start, 0);

                let skip = if starts_at_zero {
                    String::new()
                } else {
                    format!(".skip({})", snippet(cx, start.span, ".."))
                };

                let mut end_is_start_plus_val = false;

                let take = if let Some(end) = *end {
                    let mut take_expr = end;

                    if let ExprKind::Binary(ref op, ref left, ref right) = end.kind {
                        if let BinOpKind::Add = op.node {
                            let start_equal_left = SpanlessEq::new(cx).eq_expr(start, left);
                            let start_equal_right = SpanlessEq::new(cx).eq_expr(start, right);

                            if start_equal_left {
                                take_expr = right;
                            } else if start_equal_right {
                                take_expr = left;
                            }

                            end_is_start_plus_val = start_equal_left | start_equal_right;
                        }
                    }

                    if is_len_call(end, indexed) || is_end_eq_array_len(cx, end, limits, indexed_ty) {
                        String::new()
                    } else {
                        match limits {
                            ast::RangeLimits::Closed => {
                                let take_expr = sugg::Sugg::hir(cx, take_expr, "<count>");
                                format!(".take({})", take_expr + sugg::ONE)
                            },
                            ast::RangeLimits::HalfOpen => format!(".take({})", snippet(cx, take_expr.span, "..")),
                        }
                    }
                } else {
                    String::new()
                };

                let (ref_mut, method) = if visitor.indexed_mut.contains(&indexed) {
                    ("mut ", "iter_mut")
                } else {
                    ("", "iter")
                };

                let take_is_empty = take.is_empty();
                let mut method_1 = take;
                let mut method_2 = skip;

                if end_is_start_plus_val {
                    mem::swap(&mut method_1, &mut method_2);
                }

                if visitor.nonindex {
                    span_lint_and_then(
                        cx,
                        NEEDLESS_RANGE_LOOP,
                        expr.span,
                        &format!("the loop variable `{}` is used to index `{}`", ident.name, indexed),
                        |diag| {
                            multispan_sugg(
                                diag,
                                "consider using an iterator",
                                vec![
                                    (pat.span, format!("({}, <item>)", ident.name)),
                                    (
                                        arg.span,
                                        format!("{}.{}().enumerate(){}{}", indexed, method, method_1, method_2),
                                    ),
                                ],
                            );
                        },
                    );
                } else {
                    let repl = if starts_at_zero && take_is_empty {
                        format!("&{}{}", ref_mut, indexed)
                    } else {
                        format!("{}.{}(){}{}", indexed, method, method_1, method_2)
                    };

                    span_lint_and_then(
                        cx,
                        NEEDLESS_RANGE_LOOP,
                        expr.span,
                        &format!(
                            "the loop variable `{}` is only used to index `{}`.",
                            ident.name, indexed
                        ),
                        |diag| {
                            multispan_sugg(
                                diag,
                                "consider using an iterator",
                                vec![(pat.span, "<item>".to_string()), (arg.span, repl)],
                            );
                        },
                    );
                }
            }
        }
    }
}

fn is_len_call(expr: &Expr<'_>, var: Name) -> bool {
    if_chain! {
        if let ExprKind::MethodCall(ref method, _, ref len_args, _) = expr.kind;
        if len_args.len() == 1;
        if method.ident.name == sym!(len);
        if let ExprKind::Path(QPath::Resolved(_, ref path)) = len_args[0].kind;
        if path.segments.len() == 1;
        if path.segments[0].ident.name == var;
        then {
            return true;
        }
    }

    false
}

fn is_end_eq_array_len<'tcx>(
    cx: &LateContext<'tcx>,
    end: &Expr<'_>,
    limits: ast::RangeLimits,
    indexed_ty: Ty<'tcx>,
) -> bool {
    if_chain! {
        if let ExprKind::Lit(ref lit) = end.kind;
        if let ast::LitKind::Int(end_int, _) = lit.node;
        if let ty::Array(_, arr_len_const) = indexed_ty.kind;
        if let Some(arr_len) = arr_len_const.try_eval_usize(cx.tcx, cx.param_env);
        then {
            return match limits {
                ast::RangeLimits::Closed => end_int + 1 >= arr_len.into(),
                ast::RangeLimits::HalfOpen => end_int >= arr_len.into(),
            };
        }
    }

    false
}

fn lint_iter_method(cx: &LateContext<'_>, args: &[Expr<'_>], arg: &Expr<'_>, method_name: &str) {
    let mut applicability = Applicability::MachineApplicable;
    let object = snippet_with_applicability(cx, args[0].span, "_", &mut applicability);
    let muta = if method_name == "iter_mut" { "mut " } else { "" };
    span_lint_and_sugg(
        cx,
        EXPLICIT_ITER_LOOP,
        arg.span,
        "it is more concise to loop over references to containers instead of using explicit \
         iteration methods",
        "to write this more concisely, try",
        format!("&{}{}", muta, object),
        applicability,
    )
}

fn check_for_loop_arg(cx: &LateContext<'_>, pat: &Pat<'_>, arg: &Expr<'_>, expr: &Expr<'_>) {
    let mut next_loop_linted = false; // whether or not ITER_NEXT_LOOP lint was used
    if let ExprKind::MethodCall(ref method, _, ref args, _) = arg.kind {
        // just the receiver, no arguments
        if args.len() == 1 {
            let method_name = &*method.ident.as_str();
            // check for looping over x.iter() or x.iter_mut(), could use &x or &mut x
            if method_name == "iter" || method_name == "iter_mut" {
                if is_ref_iterable_type(cx, &args[0]) {
                    lint_iter_method(cx, args, arg, method_name);
                }
            } else if method_name == "into_iter" && match_trait_method(cx, arg, &paths::INTO_ITERATOR) {
                let receiver_ty = cx.tables().expr_ty(&args[0]);
                let receiver_ty_adjusted = cx.tables().expr_ty_adjusted(&args[0]);
                if TyS::same_type(receiver_ty, receiver_ty_adjusted) {
                    let mut applicability = Applicability::MachineApplicable;
                    let object = snippet_with_applicability(cx, args[0].span, "_", &mut applicability);
                    span_lint_and_sugg(
                        cx,
                        EXPLICIT_INTO_ITER_LOOP,
                        arg.span,
                        "it is more concise to loop over containers instead of using explicit \
                         iteration methods",
                        "to write this more concisely, try",
                        object.to_string(),
                        applicability,
                    );
                } else {
                    let ref_receiver_ty = cx.tcx.mk_ref(
                        cx.tcx.lifetimes.re_erased,
                        ty::TypeAndMut {
                            ty: receiver_ty,
                            mutbl: Mutability::Not,
                        },
                    );
                    if TyS::same_type(receiver_ty_adjusted, ref_receiver_ty) {
                        lint_iter_method(cx, args, arg, method_name)
                    }
                }
            } else if method_name == "next" && match_trait_method(cx, arg, &paths::ITERATOR) {
                span_lint(
                    cx,
                    ITER_NEXT_LOOP,
                    expr.span,
                    "you are iterating over `Iterator::next()` which is an Option; this will compile but is \
                    probably not what you want",
                );
                next_loop_linted = true;
            }
        }
    }
    if !next_loop_linted {
        check_arg_type(cx, pat, arg);
    }
}

/// Checks for `for` loops over `Option`s and `Result`s.
fn check_arg_type(cx: &LateContext<'_>, pat: &Pat<'_>, arg: &Expr<'_>) {
    let ty = cx.tables().expr_ty(arg);
    if is_type_diagnostic_item(cx, ty, sym!(option_type)) {
        span_lint_and_help(
            cx,
            FOR_LOOPS_OVER_FALLIBLES,
            arg.span,
            &format!(
                "for loop over `{0}`, which is an `Option`. This is more readably written as an \
                `if let` statement.",
                snippet(cx, arg.span, "_")
            ),
            None,
            &format!(
                "consider replacing `for {0} in {1}` with `if let Some({0}) = {1}`",
                snippet(cx, pat.span, "_"),
                snippet(cx, arg.span, "_")
            ),
        );
    } else if is_type_diagnostic_item(cx, ty, sym!(result_type)) {
        span_lint_and_help(
            cx,
            FOR_LOOPS_OVER_FALLIBLES,
            arg.span,
            &format!(
                "for loop over `{0}`, which is a `Result`. This is more readably written as an \
                `if let` statement.",
                snippet(cx, arg.span, "_")
            ),
            None,
            &format!(
                "consider replacing `for {0} in {1}` with `if let Ok({0}) = {1}`",
                snippet(cx, pat.span, "_"),
                snippet(cx, arg.span, "_")
            ),
        );
    }
}

fn check_for_loop_explicit_counter<'tcx>(
    cx: &LateContext<'tcx>,
    pat: &'tcx Pat<'_>,
    arg: &'tcx Expr<'_>,
    body: &'tcx Expr<'_>,
    expr: &'tcx Expr<'_>,
) {
    // Look for variables that are incremented once per loop iteration.
    let mut visitor = IncrementVisitor {
        cx,
        states: FxHashMap::default(),
        depth: 0,
        done: false,
    };
    walk_expr(&mut visitor, body);

    // For each candidate, check the parent block to see if
    // it's initialized to zero at the start of the loop.
    if let Some(block) = get_enclosing_block(&cx, expr.hir_id) {
        for (id, _) in visitor.states.iter().filter(|&(_, v)| *v == VarState::IncrOnce) {
            let mut visitor2 = InitializeVisitor {
                cx,
                end_expr: expr,
                var_id: *id,
                state: VarState::IncrOnce,
                name: None,
                depth: 0,
                past_loop: false,
            };
            walk_block(&mut visitor2, block);

            if visitor2.state == VarState::Warn {
                if let Some(name) = visitor2.name {
                    let mut applicability = Applicability::MachineApplicable;

                    // for some reason this is the only way to get the `Span`
                    // of the entire `for` loop
                    let for_span = if let ExprKind::Match(_, arms, _) = &expr.kind {
                        arms[0].body.span
                    } else {
                        unreachable!()
                    };

                    span_lint_and_sugg(
                        cx,
                        EXPLICIT_COUNTER_LOOP,
                        for_span.with_hi(arg.span.hi()),
                        &format!("the variable `{}` is used as a loop counter.", name),
                        "consider using",
                        format!(
                            "for ({}, {}) in {}.enumerate()",
                            name,
                            snippet_with_applicability(cx, pat.span, "item", &mut applicability),
                            make_iterator_snippet(cx, arg, &mut applicability),
                        ),
                        applicability,
                    );
                }
            }
        }
    }
}

/// If `arg` was the argument to a `for` loop, return the "cleanest" way of writing the
/// actual `Iterator` that the loop uses.
fn make_iterator_snippet(cx: &LateContext<'_>, arg: &Expr<'_>, applic_ref: &mut Applicability) -> String {
    let impls_iterator = get_trait_def_id(cx, &paths::ITERATOR)
        .map_or(false, |id| implements_trait(cx, cx.tables().expr_ty(arg), id, &[]));
    if impls_iterator {
        format!(
            "{}",
            sugg::Sugg::hir_with_applicability(cx, arg, "_", applic_ref).maybe_par()
        )
    } else {
        // (&x).into_iter() ==> x.iter()
        // (&mut x).into_iter() ==> x.iter_mut()
        match &arg.kind {
            ExprKind::AddrOf(BorrowKind::Ref, mutability, arg_inner)
                if has_iter_method(cx, cx.tables().expr_ty(&arg_inner)).is_some() =>
            {
                let meth_name = match mutability {
                    Mutability::Mut => "iter_mut",
                    Mutability::Not => "iter",
                };
                format!(
                    "{}.{}()",
                    sugg::Sugg::hir_with_applicability(cx, &arg_inner, "_", applic_ref).maybe_par(),
                    meth_name,
                )
            },
            _ => format!(
                "{}.into_iter()",
                sugg::Sugg::hir_with_applicability(cx, arg, "_", applic_ref).maybe_par()
            ),
        }
    }
}

/// Checks for the `FOR_KV_MAP` lint.
fn check_for_loop_over_map_kv<'tcx>(
    cx: &LateContext<'tcx>,
    pat: &'tcx Pat<'_>,
    arg: &'tcx Expr<'_>,
    body: &'tcx Expr<'_>,
    expr: &'tcx Expr<'_>,
) {
    let pat_span = pat.span;

    if let PatKind::Tuple(ref pat, _) = pat.kind {
        if pat.len() == 2 {
            let arg_span = arg.span;
            let (new_pat_span, kind, ty, mutbl) = match cx.tables().expr_ty(arg).kind {
                ty::Ref(_, ty, mutbl) => match (&pat[0].kind, &pat[1].kind) {
                    (key, _) if pat_is_wild(key, body) => (pat[1].span, "value", ty, mutbl),
                    (_, value) if pat_is_wild(value, body) => (pat[0].span, "key", ty, Mutability::Not),
                    _ => return,
                },
                _ => return,
            };
            let mutbl = match mutbl {
                Mutability::Not => "",
                Mutability::Mut => "_mut",
            };
            let arg = match arg.kind {
                ExprKind::AddrOf(BorrowKind::Ref, _, ref expr) => &**expr,
                _ => arg,
            };

            if is_type_diagnostic_item(cx, ty, sym!(hashmap_type)) || match_type(cx, ty, &paths::BTREEMAP) {
                span_lint_and_then(
                    cx,
                    FOR_KV_MAP,
                    expr.span,
                    &format!("you seem to want to iterate on a map's {}s", kind),
                    |diag| {
                        let map = sugg::Sugg::hir(cx, arg, "map");
                        multispan_sugg(
                            diag,
                            "use the corresponding method",
                            vec![
                                (pat_span, snippet(cx, new_pat_span, kind).into_owned()),
                                (arg_span, format!("{}.{}s{}()", map.maybe_par(), kind, mutbl)),
                            ],
                        );
                    },
                );
            }
        }
    }
}

struct MutatePairDelegate<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,
    hir_id_low: Option<HirId>,
    hir_id_high: Option<HirId>,
    span_low: Option<Span>,
    span_high: Option<Span>,
}

impl<'tcx> Delegate<'tcx> for MutatePairDelegate<'_, 'tcx> {
    fn consume(&mut self, _: &PlaceWithHirId<'tcx>, _: ConsumeMode) {}

    fn borrow(&mut self, cmt: &PlaceWithHirId<'tcx>, bk: ty::BorrowKind) {
        if let ty::BorrowKind::MutBorrow = bk {
            if let PlaceBase::Local(id) = cmt.place.base {
                if Some(id) == self.hir_id_low {
                    self.span_low = Some(self.cx.tcx.hir().span(cmt.hir_id))
                }
                if Some(id) == self.hir_id_high {
                    self.span_high = Some(self.cx.tcx.hir().span(cmt.hir_id))
                }
            }
        }
    }

    fn mutate(&mut self, cmt: &PlaceWithHirId<'tcx>) {
        if let PlaceBase::Local(id) = cmt.place.base {
            if Some(id) == self.hir_id_low {
                self.span_low = Some(self.cx.tcx.hir().span(cmt.hir_id))
            }
            if Some(id) == self.hir_id_high {
                self.span_high = Some(self.cx.tcx.hir().span(cmt.hir_id))
            }
        }
    }
}

impl MutatePairDelegate<'_, '_> {
    fn mutation_span(&self) -> (Option<Span>, Option<Span>) {
        (self.span_low, self.span_high)
    }
}

fn check_for_mut_range_bound(cx: &LateContext<'_>, arg: &Expr<'_>, body: &Expr<'_>) {
    if let Some(higher::Range {
        start: Some(start),
        end: Some(end),
        ..
    }) = higher::range(cx, arg)
    {
        let mut_ids = vec![check_for_mutability(cx, start), check_for_mutability(cx, end)];
        if mut_ids[0].is_some() || mut_ids[1].is_some() {
            let (span_low, span_high) = check_for_mutation(cx, body, &mut_ids);
            mut_warn_with_span(cx, span_low);
            mut_warn_with_span(cx, span_high);
        }
    }
}

fn mut_warn_with_span(cx: &LateContext<'_>, span: Option<Span>) {
    if let Some(sp) = span {
        span_lint(
            cx,
            MUT_RANGE_BOUND,
            sp,
            "attempt to mutate range bound within loop; note that the range of the loop is unchanged",
        );
    }
}

fn check_for_mutability(cx: &LateContext<'_>, bound: &Expr<'_>) -> Option<HirId> {
    if_chain! {
        if let ExprKind::Path(ref qpath) = bound.kind;
        if let QPath::Resolved(None, _) = *qpath;
        then {
            let res = qpath_res(cx, qpath, bound.hir_id);
            if let Res::Local(hir_id) = res {
                let node_str = cx.tcx.hir().get(hir_id);
                if_chain! {
                    if let Node::Binding(pat) = node_str;
                    if let PatKind::Binding(bind_ann, ..) = pat.kind;
                    if let BindingAnnotation::Mutable = bind_ann;
                    then {
                        return Some(hir_id);
                    }
                }
            }
        }
    }
    None
}

fn check_for_mutation<'tcx>(
    cx: &LateContext<'tcx>,
    body: &Expr<'_>,
    bound_ids: &[Option<HirId>],
) -> (Option<Span>, Option<Span>) {
    let mut delegate = MutatePairDelegate {
        cx,
        hir_id_low: bound_ids[0],
        hir_id_high: bound_ids[1],
        span_low: None,
        span_high: None,
    };
    let def_id = body.hir_id.owner.to_def_id();
    cx.tcx.infer_ctxt().enter(|infcx| {
        ExprUseVisitor::new(&mut delegate, &infcx, def_id.expect_local(), cx.param_env, cx.tables()).walk_expr(body);
    });
    delegate.mutation_span()
}

/// Returns `true` if the pattern is a `PatWild` or an ident prefixed with `_`.
fn pat_is_wild<'tcx>(pat: &'tcx PatKind<'_>, body: &'tcx Expr<'_>) -> bool {
    match *pat {
        PatKind::Wild => true,
        PatKind::Binding(.., ident, None) if ident.as_str().starts_with('_') => is_unused(&ident, body),
        _ => false,
    }
}

struct LocalUsedVisitor<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,
    local: HirId,
    used: bool,
}

impl<'a, 'tcx> Visitor<'tcx> for LocalUsedVisitor<'a, 'tcx> {
    type Map = Map<'tcx>;

    fn visit_expr(&mut self, expr: &'tcx Expr<'_>) {
        if same_var(self.cx, expr, self.local) {
            self.used = true;
        } else {
            walk_expr(self, expr);
        }
    }

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::None
    }
}

struct VarVisitor<'a, 'tcx> {
    /// context reference
    cx: &'a LateContext<'tcx>,
    /// var name to look for as index
    var: HirId,
    /// indexed variables that are used mutably
    indexed_mut: FxHashSet<Name>,
    /// indirectly indexed variables (`v[(i + 4) % N]`), the extend is `None` for global
    indexed_indirectly: FxHashMap<Name, Option<region::Scope>>,
    /// subset of `indexed` of vars that are indexed directly: `v[i]`
    /// this will not contain cases like `v[calc_index(i)]` or `v[(i + 4) % N]`
    indexed_directly: FxHashMap<Name, (Option<region::Scope>, Ty<'tcx>)>,
    /// Any names that are used outside an index operation.
    /// Used to detect things like `&mut vec` used together with `vec[i]`
    referenced: FxHashSet<Name>,
    /// has the loop variable been used in expressions other than the index of
    /// an index op?
    nonindex: bool,
    /// Whether we are inside the `$` in `&mut $` or `$ = foo` or `$.bar`, where bar
    /// takes `&mut self`
    prefer_mutable: bool,
}

impl<'a, 'tcx> VarVisitor<'a, 'tcx> {
    fn check(&mut self, idx: &'tcx Expr<'_>, seqexpr: &'tcx Expr<'_>, expr: &'tcx Expr<'_>) -> bool {
        if_chain! {
            // the indexed container is referenced by a name
            if let ExprKind::Path(ref seqpath) = seqexpr.kind;
            if let QPath::Resolved(None, ref seqvar) = *seqpath;
            if seqvar.segments.len() == 1;
            then {
                let index_used_directly = same_var(self.cx, idx, self.var);
                let indexed_indirectly = {
                    let mut used_visitor = LocalUsedVisitor {
                        cx: self.cx,
                        local: self.var,
                        used: false,
                    };
                    walk_expr(&mut used_visitor, idx);
                    used_visitor.used
                };

                if indexed_indirectly || index_used_directly {
                    if self.prefer_mutable {
                        self.indexed_mut.insert(seqvar.segments[0].ident.name);
                    }
                    let res = qpath_res(self.cx, seqpath, seqexpr.hir_id);
                    match res {
                        Res::Local(hir_id) => {
                            let parent_id = self.cx.tcx.hir().get_parent_item(expr.hir_id);
                            let parent_def_id = self.cx.tcx.hir().local_def_id(parent_id);
                            let extent = self.cx.tcx.region_scope_tree(parent_def_id).var_scope(hir_id.local_id);
                            if indexed_indirectly {
                                self.indexed_indirectly.insert(seqvar.segments[0].ident.name, Some(extent));
                            }
                            if index_used_directly {
                                self.indexed_directly.insert(
                                    seqvar.segments[0].ident.name,
                                    (Some(extent), self.cx.tables().node_type(seqexpr.hir_id)),
                                );
                            }
                            return false;  // no need to walk further *on the variable*
                        }
                        Res::Def(DefKind::Static | DefKind::Const, ..) => {
                            if indexed_indirectly {
                                self.indexed_indirectly.insert(seqvar.segments[0].ident.name, None);
                            }
                            if index_used_directly {
                                self.indexed_directly.insert(
                                    seqvar.segments[0].ident.name,
                                    (None, self.cx.tables().node_type(seqexpr.hir_id)),
                                );
                            }
                            return false;  // no need to walk further *on the variable*
                        }
                        _ => (),
                    }
                }
            }
        }
        true
    }
}

impl<'a, 'tcx> Visitor<'tcx> for VarVisitor<'a, 'tcx> {
    type Map = Map<'tcx>;

    fn visit_expr(&mut self, expr: &'tcx Expr<'_>) {
        if_chain! {
            // a range index op
            if let ExprKind::MethodCall(ref meth, _, ref args, _) = expr.kind;
            if (meth.ident.name == sym!(index) && match_trait_method(self.cx, expr, &paths::INDEX))
                || (meth.ident.name == sym!(index_mut) && match_trait_method(self.cx, expr, &paths::INDEX_MUT));
            if !self.check(&args[1], &args[0], expr);
            then { return }
        }

        if_chain! {
            // an index op
            if let ExprKind::Index(ref seqexpr, ref idx) = expr.kind;
            if !self.check(idx, seqexpr, expr);
            then { return }
        }

        if_chain! {
            // directly using a variable
            if let ExprKind::Path(ref qpath) = expr.kind;
            if let QPath::Resolved(None, ref path) = *qpath;
            if path.segments.len() == 1;
            then {
                if let Res::Local(local_id) = qpath_res(self.cx, qpath, expr.hir_id) {
                    if local_id == self.var {
                        self.nonindex = true;
                    } else {
                        // not the correct variable, but still a variable
                        self.referenced.insert(path.segments[0].ident.name);
                    }
                }
            }
        }

        let old = self.prefer_mutable;
        match expr.kind {
            ExprKind::AssignOp(_, ref lhs, ref rhs) | ExprKind::Assign(ref lhs, ref rhs, _) => {
                self.prefer_mutable = true;
                self.visit_expr(lhs);
                self.prefer_mutable = false;
                self.visit_expr(rhs);
            },
            ExprKind::AddrOf(BorrowKind::Ref, mutbl, ref expr) => {
                if mutbl == Mutability::Mut {
                    self.prefer_mutable = true;
                }
                self.visit_expr(expr);
            },
            ExprKind::Call(ref f, args) => {
                self.visit_expr(f);
                for expr in args {
                    let ty = self.cx.tables().expr_ty_adjusted(expr);
                    self.prefer_mutable = false;
                    if let ty::Ref(_, _, mutbl) = ty.kind {
                        if mutbl == Mutability::Mut {
                            self.prefer_mutable = true;
                        }
                    }
                    self.visit_expr(expr);
                }
            },
            ExprKind::MethodCall(_, _, args, _) => {
                let def_id = self.cx.tables().type_dependent_def_id(expr.hir_id).unwrap();
                for (ty, expr) in self.cx.tcx.fn_sig(def_id).inputs().skip_binder().iter().zip(args) {
                    self.prefer_mutable = false;
                    if let ty::Ref(_, _, mutbl) = ty.kind {
                        if mutbl == Mutability::Mut {
                            self.prefer_mutable = true;
                        }
                    }
                    self.visit_expr(expr);
                }
            },
            ExprKind::Closure(_, _, body_id, ..) => {
                let body = self.cx.tcx.hir().body(body_id);
                self.visit_expr(&body.value);
            },
            _ => walk_expr(self, expr),
        }
        self.prefer_mutable = old;
    }
    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::None
    }
}

fn is_used_inside<'tcx>(cx: &LateContext<'tcx>, expr: &'tcx Expr<'_>, container: &'tcx Expr<'_>) -> bool {
    let def_id = match var_def_id(cx, expr) {
        Some(id) => id,
        None => return false,
    };
    if let Some(used_mutably) = mutated_variables(container, cx) {
        if used_mutably.contains(&def_id) {
            return true;
        }
    }
    false
}

fn is_iterator_used_after_while_let<'tcx>(cx: &LateContext<'tcx>, iter_expr: &'tcx Expr<'_>) -> bool {
    let def_id = match var_def_id(cx, iter_expr) {
        Some(id) => id,
        None => return false,
    };
    let mut visitor = VarUsedAfterLoopVisitor {
        cx,
        def_id,
        iter_expr_id: iter_expr.hir_id,
        past_while_let: false,
        var_used_after_while_let: false,
    };
    if let Some(enclosing_block) = get_enclosing_block(cx, def_id) {
        walk_block(&mut visitor, enclosing_block);
    }
    visitor.var_used_after_while_let
}

struct VarUsedAfterLoopVisitor<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,
    def_id: HirId,
    iter_expr_id: HirId,
    past_while_let: bool,
    var_used_after_while_let: bool,
}

impl<'a, 'tcx> Visitor<'tcx> for VarUsedAfterLoopVisitor<'a, 'tcx> {
    type Map = Map<'tcx>;

    fn visit_expr(&mut self, expr: &'tcx Expr<'_>) {
        if self.past_while_let {
            if Some(self.def_id) == var_def_id(self.cx, expr) {
                self.var_used_after_while_let = true;
            }
        } else if self.iter_expr_id == expr.hir_id {
            self.past_while_let = true;
        }
        walk_expr(self, expr);
    }
    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::None
    }
}

/// Returns `true` if the type of expr is one that provides `IntoIterator` impls
/// for `&T` and `&mut T`, such as `Vec`.
#[rustfmt::skip]
fn is_ref_iterable_type(cx: &LateContext<'_>, e: &Expr<'_>) -> bool {
    // no walk_ptrs_ty: calling iter() on a reference can make sense because it
    // will allow further borrows afterwards
    let ty = cx.tables().expr_ty(e);
    is_iterable_array(ty, cx) ||
    is_type_diagnostic_item(cx, ty, sym!(vec_type)) ||
    match_type(cx, ty, &paths::LINKED_LIST) ||
    is_type_diagnostic_item(cx, ty, sym!(hashmap_type)) ||
    is_type_diagnostic_item(cx, ty, sym!(hashset_type)) ||
    is_type_diagnostic_item(cx, ty, sym!(vecdeque_type)) ||
    match_type(cx, ty, &paths::BINARY_HEAP) ||
    match_type(cx, ty, &paths::BTREEMAP) ||
    match_type(cx, ty, &paths::BTREESET)
}

fn is_iterable_array<'tcx>(ty: Ty<'tcx>, cx: &LateContext<'tcx>) -> bool {
    // IntoIterator is currently only implemented for array sizes <= 32 in rustc
    match ty.kind {
        ty::Array(_, n) => {
            if let Some(val) = n.try_eval_usize(cx.tcx, cx.param_env) {
                (0..=32).contains(&val)
            } else {
                false
            }
        },
        _ => false,
    }
}

/// If a block begins with a statement (possibly a `let` binding) and has an
/// expression, return it.
fn extract_expr_from_first_stmt<'tcx>(block: &Block<'tcx>) -> Option<&'tcx Expr<'tcx>> {
    if block.stmts.is_empty() {
        return None;
    }
    if let StmtKind::Local(ref local) = block.stmts[0].kind {
        if let Some(expr) = local.init {
            Some(expr)
        } else {
            None
        }
    } else {
        None
    }
}

/// If a block begins with an expression (with or without semicolon), return it.
fn extract_first_expr<'tcx>(block: &Block<'tcx>) -> Option<&'tcx Expr<'tcx>> {
    match block.expr {
        Some(ref expr) if block.stmts.is_empty() => Some(expr),
        None if !block.stmts.is_empty() => match block.stmts[0].kind {
            StmtKind::Expr(ref expr) | StmtKind::Semi(ref expr) => Some(expr),
            StmtKind::Local(..) | StmtKind::Item(..) => None,
        },
        _ => None,
    }
}

/// Returns `true` if expr contains a single break expr without destination label
/// and
/// passed expression. The expression may be within a block.
fn is_simple_break_expr(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Break(dest, ref passed_expr) if dest.label.is_none() && passed_expr.is_none() => true,
        ExprKind::Block(ref b, _) => extract_first_expr(b).map_or(false, |subexpr| is_simple_break_expr(subexpr)),
        _ => false,
    }
}

// To trigger the EXPLICIT_COUNTER_LOOP lint, a variable must be
// incremented exactly once in the loop body, and initialized to zero
// at the start of the loop.
#[derive(Debug, PartialEq)]
enum VarState {
    Initial,  // Not examined yet
    IncrOnce, // Incremented exactly once, may be a loop counter
    Declared, // Declared but not (yet) initialized to zero
    Warn,
    DontWarn,
}

/// Scan a for loop for variables that are incremented exactly once.
struct IncrementVisitor<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,          // context reference
    states: FxHashMap<HirId, VarState>, // incremented variables
    depth: u32,                         // depth of conditional expressions
    done: bool,
}

impl<'a, 'tcx> Visitor<'tcx> for IncrementVisitor<'a, 'tcx> {
    type Map = Map<'tcx>;

    fn visit_expr(&mut self, expr: &'tcx Expr<'_>) {
        if self.done {
            return;
        }

        // If node is a variable
        if let Some(def_id) = var_def_id(self.cx, expr) {
            if let Some(parent) = get_parent_expr(self.cx, expr) {
                let state = self.states.entry(def_id).or_insert(VarState::Initial);

                match parent.kind {
                    ExprKind::AssignOp(op, ref lhs, ref rhs) => {
                        if lhs.hir_id == expr.hir_id {
                            if op.node == BinOpKind::Add && is_integer_const(self.cx, rhs, 1) {
                                *state = match *state {
                                    VarState::Initial if self.depth == 0 => VarState::IncrOnce,
                                    _ => VarState::DontWarn,
                                };
                            } else {
                                // Assigned some other value
                                *state = VarState::DontWarn;
                            }
                        }
                    },
                    ExprKind::Assign(ref lhs, _, _) if lhs.hir_id == expr.hir_id => *state = VarState::DontWarn,
                    ExprKind::AddrOf(BorrowKind::Ref, mutability, _) if mutability == Mutability::Mut => {
                        *state = VarState::DontWarn
                    },
                    _ => (),
                }
            }
        } else if is_loop(expr) || is_conditional(expr) {
            self.depth += 1;
            walk_expr(self, expr);
            self.depth -= 1;
            return;
        } else if let ExprKind::Continue(_) = expr.kind {
            self.done = true;
            return;
        }
        walk_expr(self, expr);
    }
    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::None
    }
}

/// Checks whether a variable is initialized to zero at the start of a loop.
struct InitializeVisitor<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,  // context reference
    end_expr: &'tcx Expr<'tcx>, // the for loop. Stop scanning here.
    var_id: HirId,
    state: VarState,
    name: Option<Name>,
    depth: u32, // depth of conditional expressions
    past_loop: bool,
}

impl<'a, 'tcx> Visitor<'tcx> for InitializeVisitor<'a, 'tcx> {
    type Map = Map<'tcx>;

    fn visit_stmt(&mut self, stmt: &'tcx Stmt<'_>) {
        // Look for declarations of the variable
        if let StmtKind::Local(ref local) = stmt.kind {
            if local.pat.hir_id == self.var_id {
                if let PatKind::Binding(.., ident, _) = local.pat.kind {
                    self.name = Some(ident.name);

                    self.state = if let Some(ref init) = local.init {
                        if is_integer_const(&self.cx, init, 0) {
                            VarState::Warn
                        } else {
                            VarState::Declared
                        }
                    } else {
                        VarState::Declared
                    }
                }
            }
        }
        walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'_>) {
        if self.state == VarState::DontWarn {
            return;
        }
        if expr.hir_id == self.end_expr.hir_id {
            self.past_loop = true;
            return;
        }
        // No need to visit expressions before the variable is
        // declared
        if self.state == VarState::IncrOnce {
            return;
        }

        // If node is the desired variable, see how it's used
        if var_def_id(self.cx, expr) == Some(self.var_id) {
            if let Some(parent) = get_parent_expr(self.cx, expr) {
                match parent.kind {
                    ExprKind::AssignOp(_, ref lhs, _) if lhs.hir_id == expr.hir_id => {
                        self.state = VarState::DontWarn;
                    },
                    ExprKind::Assign(ref lhs, ref rhs, _) if lhs.hir_id == expr.hir_id => {
                        self.state = if is_integer_const(&self.cx, rhs, 0) && self.depth == 0 {
                            VarState::Warn
                        } else {
                            VarState::DontWarn
                        }
                    },
                    ExprKind::AddrOf(BorrowKind::Ref, mutability, _) if mutability == Mutability::Mut => {
                        self.state = VarState::DontWarn
                    },
                    _ => (),
                }
            }

            if self.past_loop {
                self.state = VarState::DontWarn;
                return;
            }
        } else if !self.past_loop && is_loop(expr) {
            self.state = VarState::DontWarn;
            return;
        } else if is_conditional(expr) {
            self.depth += 1;
            walk_expr(self, expr);
            self.depth -= 1;
            return;
        }
        walk_expr(self, expr);
    }

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::OnlyBodies(self.cx.tcx.hir())
    }
}

fn var_def_id(cx: &LateContext<'_>, expr: &Expr<'_>) -> Option<HirId> {
    if let ExprKind::Path(ref qpath) = expr.kind {
        let path_res = qpath_res(cx, qpath, expr.hir_id);
        if let Res::Local(hir_id) = path_res {
            return Some(hir_id);
        }
    }
    None
}

fn is_loop(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Loop(..) => true,
        _ => false,
    }
}

fn is_conditional(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Match(..) => true,
        _ => false,
    }
}

fn is_nested(cx: &LateContext<'_>, match_expr: &Expr<'_>, iter_expr: &Expr<'_>) -> bool {
    if_chain! {
        if let Some(loop_block) = get_enclosing_block(cx, match_expr.hir_id);
        let parent_node = cx.tcx.hir().get_parent_node(loop_block.hir_id);
        if let Some(Node::Expr(loop_expr)) = cx.tcx.hir().find(parent_node);
        then {
            return is_loop_nested(cx, loop_expr, iter_expr)
        }
    }
    false
}

fn is_loop_nested(cx: &LateContext<'_>, loop_expr: &Expr<'_>, iter_expr: &Expr<'_>) -> bool {
    let mut id = loop_expr.hir_id;
    let iter_name = if let Some(name) = path_name(iter_expr) {
        name
    } else {
        return true;
    };
    loop {
        let parent = cx.tcx.hir().get_parent_node(id);
        if parent == id {
            return false;
        }
        match cx.tcx.hir().find(parent) {
            Some(Node::Expr(expr)) => {
                if let ExprKind::Loop(..) = expr.kind {
                    return true;
                };
            },
            Some(Node::Block(block)) => {
                let mut block_visitor = LoopNestVisitor {
                    hir_id: id,
                    iterator: iter_name,
                    nesting: Unknown,
                };
                walk_block(&mut block_visitor, block);
                if block_visitor.nesting == RuledOut {
                    return false;
                }
            },
            Some(Node::Stmt(_)) => (),
            _ => {
                return false;
            },
        }
        id = parent;
    }
}

#[derive(PartialEq, Eq)]
enum Nesting {
    Unknown,     // no nesting detected yet
    RuledOut,    // the iterator is initialized or assigned within scope
    LookFurther, // no nesting detected, no further walk required
}

use self::Nesting::{LookFurther, RuledOut, Unknown};

struct LoopNestVisitor {
    hir_id: HirId,
    iterator: Name,
    nesting: Nesting,
}

impl<'tcx> Visitor<'tcx> for LoopNestVisitor {
    type Map = Map<'tcx>;

    fn visit_stmt(&mut self, stmt: &'tcx Stmt<'_>) {
        if stmt.hir_id == self.hir_id {
            self.nesting = LookFurther;
        } else if self.nesting == Unknown {
            walk_stmt(self, stmt);
        }
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'_>) {
        if self.nesting != Unknown {
            return;
        }
        if expr.hir_id == self.hir_id {
            self.nesting = LookFurther;
            return;
        }
        match expr.kind {
            ExprKind::Assign(ref path, _, _) | ExprKind::AssignOp(_, ref path, _) => {
                if match_var(path, self.iterator) {
                    self.nesting = RuledOut;
                }
            },
            _ => walk_expr(self, expr),
        }
    }

    fn visit_pat(&mut self, pat: &'tcx Pat<'_>) {
        if self.nesting != Unknown {
            return;
        }
        if let PatKind::Binding(.., span_name, _) = pat.kind {
            if self.iterator == span_name.name {
                self.nesting = RuledOut;
                return;
            }
        }
        walk_pat(self, pat)
    }

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::None
    }
}

fn path_name(e: &Expr<'_>) -> Option<Name> {
    if let ExprKind::Path(QPath::Resolved(_, ref path)) = e.kind {
        let segments = &path.segments;
        if segments.len() == 1 {
            return Some(segments[0].ident.name);
        }
    };
    None
}

fn check_infinite_loop<'tcx>(cx: &LateContext<'tcx>, cond: &'tcx Expr<'_>, expr: &'tcx Expr<'_>) {
    if constant(cx, cx.tables(), cond).is_some() {
        // A pure constant condition (e.g., `while false`) is not linted.
        return;
    }

    let mut var_visitor = VarCollectorVisitor {
        cx,
        ids: FxHashSet::default(),
        def_ids: FxHashMap::default(),
        skip: false,
    };
    var_visitor.visit_expr(cond);
    if var_visitor.skip {
        return;
    }
    let used_in_condition = &var_visitor.ids;
    let no_cond_variable_mutated = if let Some(used_mutably) = mutated_variables(expr, cx) {
        used_in_condition.is_disjoint(&used_mutably)
    } else {
        return;
    };
    let mutable_static_in_cond = var_visitor.def_ids.iter().any(|(_, v)| *v);

    let mut has_break_or_return_visitor = HasBreakOrReturnVisitor {
        has_break_or_return: false,
    };
    has_break_or_return_visitor.visit_expr(expr);
    let has_break_or_return = has_break_or_return_visitor.has_break_or_return;

    if no_cond_variable_mutated && !mutable_static_in_cond {
        span_lint_and_then(
            cx,
            WHILE_IMMUTABLE_CONDITION,
            cond.span,
            "variables in the condition are not mutated in the loop body",
            |diag| {
                diag.note("this may lead to an infinite or to a never running loop");

                if has_break_or_return {
                    diag.note("this loop contains `return`s or `break`s");
                    diag.help("rewrite it as `if cond { loop { } }`");
                }
            },
        );
    }
}

struct HasBreakOrReturnVisitor {
    has_break_or_return: bool,
}

impl<'tcx> Visitor<'tcx> for HasBreakOrReturnVisitor {
    type Map = Map<'tcx>;

    fn visit_expr(&mut self, expr: &'tcx Expr<'_>) {
        if self.has_break_or_return {
            return;
        }

        match expr.kind {
            ExprKind::Ret(_) | ExprKind::Break(_, _) => {
                self.has_break_or_return = true;
                return;
            },
            _ => {},
        }

        walk_expr(self, expr);
    }

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::None
    }
}

/// Collects the set of variables in an expression
/// Stops analysis if a function call is found
/// Note: In some cases such as `self`, there are no mutable annotation,
/// All variables definition IDs are collected
struct VarCollectorVisitor<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,
    ids: FxHashSet<HirId>,
    def_ids: FxHashMap<def_id::DefId, bool>,
    skip: bool,
}

impl<'a, 'tcx> VarCollectorVisitor<'a, 'tcx> {
    fn insert_def_id(&mut self, ex: &'tcx Expr<'_>) {
        if_chain! {
            if let ExprKind::Path(ref qpath) = ex.kind;
            if let QPath::Resolved(None, _) = *qpath;
            let res = qpath_res(self.cx, qpath, ex.hir_id);
            then {
                match res {
                    Res::Local(hir_id) => {
                        self.ids.insert(hir_id);
                    },
                    Res::Def(DefKind::Static, def_id) => {
                        let mutable = self.cx.tcx.is_mutable_static(def_id);
                        self.def_ids.insert(def_id, mutable);
                    },
                    _ => {},
                }
            }
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for VarCollectorVisitor<'a, 'tcx> {
    type Map = Map<'tcx>;

    fn visit_expr(&mut self, ex: &'tcx Expr<'_>) {
        match ex.kind {
            ExprKind::Path(_) => self.insert_def_id(ex),
            // If there is any function/method call… we just stop analysis
            ExprKind::Call(..) | ExprKind::MethodCall(..) => self.skip = true,

            _ => walk_expr(self, ex),
        }
    }

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::None
    }
}

const NEEDLESS_COLLECT_MSG: &str = "avoid using `collect()` when not needed";

fn check_needless_collect<'tcx>(expr: &'tcx Expr<'_>, cx: &LateContext<'tcx>) {
    if_chain! {
        if let ExprKind::MethodCall(ref method, _, ref args, _) = expr.kind;
        if let ExprKind::MethodCall(ref chain_method, _, _, _) = args[0].kind;
        if chain_method.ident.name == sym!(collect) && match_trait_method(cx, &args[0], &paths::ITERATOR);
        if let Some(ref generic_args) = chain_method.args;
        if let Some(GenericArg::Type(ref ty)) = generic_args.args.get(0);
        then {
            let ty = cx.tables().node_type(ty.hir_id);
            if is_type_diagnostic_item(cx, ty, sym!(vec_type)) ||
                is_type_diagnostic_item(cx, ty, sym!(vecdeque_type)) ||
                match_type(cx, ty, &paths::BTREEMAP) ||
                is_type_diagnostic_item(cx, ty, sym!(hashmap_type)) {
                if method.ident.name == sym!(len) {
                    let span = shorten_span(expr, sym!(collect));
                    span_lint_and_sugg(
                        cx,
                        NEEDLESS_COLLECT,
                        span,
                        NEEDLESS_COLLECT_MSG,
                        "replace with",
                        "count()".to_string(),
                        Applicability::MachineApplicable,
                    );
                }
                if method.ident.name == sym!(is_empty) {
                    let span = shorten_span(expr, sym!(iter));
                    span_lint_and_sugg(
                        cx,
                        NEEDLESS_COLLECT,
                        span,
                        NEEDLESS_COLLECT_MSG,
                        "replace with",
                        "get(0).is_none()".to_string(),
                        Applicability::MachineApplicable,
                    );
                }
                if method.ident.name == sym!(contains) {
                    let contains_arg = snippet(cx, args[1].span, "??");
                    let span = shorten_span(expr, sym!(collect));
                    span_lint_and_then(
                        cx,
                        NEEDLESS_COLLECT,
                        span,
                        NEEDLESS_COLLECT_MSG,
                        |diag| {
                            let (arg, pred) = if contains_arg.starts_with('&') {
                                ("x", &contains_arg[1..])
                            } else {
                                ("&x", &*contains_arg)
                            };
                            diag.span_suggestion(
                                span,
                                "replace with",
                                format!(
                                    "any(|{}| x == {})",
                                    arg, pred
                                ),
                                Applicability::MachineApplicable,
                            );
                        }
                    );
                }
            }
        }
    }
}

fn shorten_span(expr: &Expr<'_>, target_fn_name: Symbol) -> Span {
    let mut current_expr = expr;
    while let ExprKind::MethodCall(ref path, ref span, ref args, _) = current_expr.kind {
        if path.ident.name == target_fn_name {
            return expr.span.with_lo(span.lo());
        }
        current_expr = &args[0];
    }
    unreachable!()
}
