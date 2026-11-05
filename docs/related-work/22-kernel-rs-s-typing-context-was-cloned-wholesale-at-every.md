## 22. kernel.rs's typing context was cloned wholesale at every binder -- found and switched to a persistent structure

`kernel.rs`'s `Ctx` (`infer`/`check`'s own typing context, threaded
through every recursive call) was a plain `Vec<Expr>`. Every binder --
`Pi`, `Lam`, `Sigma`, `Pair`, `W` -- entered its body one level deeper by
doing `let mut ctx2 = ctx.clone(); ctx2.push(...)` before recursing, at
five call sites (`infer_sigma`, `infer_pair`, and `infer`'s own `Pi`,
`Lam`, and `W` arms; `check`'s `Lam`-against-`Pi` special case makes it
six). Each `Expr` itself is cheap to clone (`Rc`-based), but the *`Vec`*
clone is O(current context length) regardless -- so a term with `k`
nested binders, checked under a context of length `L` at its deepest
point, pays O(k*L) total copying, not the O(k) the module's own
"one push per binder" design implies. Confirmed with a deliberately
deep, cheap-to-build stress term (`pi(sort(0), pi(sort(0), ... sort(0)))`
nested 800 deep, checked from an empty context via `typecheck`): 17.8ms
with the plain `Vec`, vs. 2.45ms after the fix below -- a ~7x difference
at a depth this project's own `eval_dyn`-adjacent proof search can
plausibly reach, and one that gets worse, not better, as terms grow.

Considered and rejected three alternatives before fixing this: manual
mutable push/pop (`&mut Ctx` instead of by-value clone-then-recurse) --
correctness-equivalent and allocation-free, but would have meant
threading pop-on-every-return-path through `infer`/`check`'s entire
call graph in both `kernel.rs` and `proof.rs`, in the single most
soundness-critical part of the codebase, for a purely-performance fix;
`Rc<Vec<Expr>>` plus `Rc::make_mut` -- doesn't actually help, since the
caller's own `ctx` reference stays alive across the recursive call at
every one of these sites, so the refcount is never 1 at the point
`make_mut` would need it to be, and it clones anyway; and a hand-rolled
persistent structure -- avoids a new dependency, but risks introducing a
genuinely new bug into the kernel to solve a problem an existing,
well-tested library already solves.

Fixed by switching `Ctx` to `im::Vector<Expr>` (the `im` crate, added as
a new dependency): a persistent, structurally-shared vector whose
`.clone()` and `.push_back()` are both O(log n) (amortized ~O(1) in
practice) instead of O(n). The fix is almost entirely mechanical --
`Ctx`'s definition, `Postulates::new`'s `Vec::new()` -> `Ctx::new()`,
the six `.push(...)` call sites -> `.push_back(...)`, and
`ctx_lookup`'s own `ctx[idx]` needs no change at all (`im::Vector`
implements `Index<usize>` the same way `Vec` does). The one non-trivial
spot: `close_pi`/`close_lam` (`kernel.rs`) used to take `ctx: &[Expr]`
and slice it (`ctx[base_len..]`) to find "everything pushed since
`base_len`" -- `im::Vector` has no contiguous backing store to slice, so
these now take `&Ctx` directly and use `ctx.iter().skip(base_len).rev()`
instead. Both call sites that pass `close_pi`/`close_lam` around as `fn`
pointers (`proof.rs`'s `params_and_close`/`params_and_close_typed`)
needed their pointer type updated to match (`fn(usize, &Ctx, Expr) ->
Expr`), but their own bodies -- and everywhere else that reads, clones,
or truncates `arith.p.ctx` -- needed no change: `im::Vector` already
supports `.len()`, `.clone()`, and `.truncate()` with the exact same
signatures `Vec` did.

Verified directly (not just by reasoning about complexity): reverted
`Ctx` back to `Vec<Expr>` via `git stash`, re-ran the same 800-deep
stress term, reproduced the 17.8ms baseline, then restored the fix and
confirmed the 2.45ms result again -- a real, measured improvement, not
just an asymptotic argument. Full existing suite (188 lib/bin tests, all
four fuzzers at release, `cargo clippy --all-targets`, the `cargo run
--release` demo) stayed green throughout, confirming the change is
observably behavior-preserving.

