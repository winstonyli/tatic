## 57. `def_eq` compares weak head normal forms, not full normal forms

This lands §55's second proposal. `def_eq(a, b)` used to decide
`nf(a) == nf(b)` by building both normal forms. Now `conv` reduces each
side to weak head normal form, compares the outermost constructors, and
recurses into the children, trying §56's `==` shortcut at every level.
So a part both sides share is never normalised.

**Survey.** No mature kernel normalises both sides in full.
- Lean 4's `is_def_eq_core` takes `whnf_core` of both sides, unfolds
  definitions lazily (`lazy_delta_reduction`), and compares applications
  argument by argument (`is_def_eq_app`).
- Coq's kernel conversion is a lazy machine that compares head
  constructors and their stacks, reducing only as needed.
- Agda's `compareTerm` works on weak head normal forms and compares
  eliminations one at a time.
- In the literature this is Coquand's algorithm ("An algorithm for
  type-checking dependent types", 1996), later refined by Abel and
  Coquand for eta. Every variant compares heads and recurses.

**Why it's exact.** `nf_impl(e)` is `whnf(e)`'s outermost constructor
over the `nf` of each child. So `nf(a) == nf(b)` holds exactly when the
two weak head normal forms have the same constructor (and the same index,
for `Var` and `Sort`) and each pair of children has equal normal forms,
which is what `conv` checks recursively. It answers `false` early at the
first mismatch, and never reduces anything `nf` wouldn't. tatic has no
eta rule, so there's nothing beyond this to compare.

**Options measured** (throwaway spike, reverted). `kernel::check` of the
`fib` instance proofs, best of 5, under load:

| `def_eq` | `fib(8)` | reductions (`whnf` + `nf` calls) | `fib(12)` |
|---|---|---|---|
| §56 (full `nf`) | 173 ms | 118.6k + 41.6k | 1.73 s |
| `conv` | 75 ms | 39.5k + 0 | 0.81 s |
| full `nf`, one `ReductionCache` per `check` | 146 ms | 113.4k + 40.0k | 1.52 s |
| `conv`, one cache per `check` | 66 ms | 39.4k + 0 | 0.52 s |

A shared cache barely changes the work once `conv` is in (39.4k against
39.5k reductions), and it would need either a thread-local or a cache
threaded through every `infer` signature (§50's objection). So only
`conv` landed.

**Tests.**
- `def_eq_normalises_only_where_the_sides_differ`: two `Pi`s whose
  domains are separately built copies of §56's doubling term, and whose
  codomains differ by one redex. It must finish in 5 ms. It took 415 ms
  before.
- `def_eq_agrees_with_comparing_normal_forms`: 20,000 random pairs, half
  of them the same term with different redexes inserted (`with_redexes`),
  must agree with `nf(a) == nf(b)`.
- Mutations caught: `Var`s all equal, `Sigma`'s second child skipped,
  and children compared without reducing them.

**Measured.** The bench A/B was too noisy to read. The same bench swung
from -50% to +48% between two runs. So `kernel::check` was timed on the
two over-application instance proofs, alternating the old and new
`def_eq` in one process (best of 15): 14.8 to 10.0 ms and 10.9 to 7.4 ms.

**A cost `conv` shares with `nf`.** Trying `==` at every level walks a
term once per ancestor when the first difference is deep, so conversion
is quadratic in depth in the worst case. `nf` already was, for a
different reason. On a neutral application spine, `whnf` returns
`App(Rc::new(whnf(f)), a)`, a fresh `Rc` that the pointer-keyed
`ReductionCache` misses, so each level re-reduces the spine below it.
Two spines 1,000 deep that differ only at the head take 0.81 s with `nf`
and 0.95 s with `conv`. At 4,000 deep they take 28 s and 26 s. The
corpus's terms are nowhere near that deep, but a proof with a long
neutral spine would be.

