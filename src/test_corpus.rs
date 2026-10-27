//! Terms only unit tests use, kept out of `samples` (which the demo, the
//! benches and the integration tests share). First, three `samples::source`
//! can't express: one with a free variable (the parser rejects unbound
//! names), one built programmatically past `spec_check::MAX_NODES`, and a
//! doubled DAG whose text is exponentially long. Then the shapes that unit
//! tests in several files share, as source.

use crate::samples::source;
use crate::term::{Hash, TermStore};

/// `\n. if n == 777 then (\x. 0) v5 else 1`, with `v5` unbound: `eval`
/// fails with `UnboundVariable` at `n = 777`. Contracting the redex would
/// hide that, which is why the checker requires a closed source.
pub(crate) fn open_redex_probe(s: &mut TermStore) -> Hash {
    use crate::term::PrimOp;
    let (n, zero, one, magic, v5) = (s.var(0), s.lit(0), s.lit(1), s.lit(777), s.var(5));
    let cond = s.prim(PrimOp::Eq, n, magic);
    let k0 = s.abs(zero);
    let redex = s.app(k0, v5);
    let body = s.if_(cond, redex, one);
    s.abs(body)
}

/// `\n. (\x. n) BIG`, with `BIG` a closed lambda of more than `MAX_NODES`
/// nodes (a balanced sum of `MAX_NODES` distinct literals, so about twice
/// that, and shallow enough for the recursive passes). The one βv step
/// shrinks it far below the limit, but the checker rejects the source
/// itself for its size.
pub(crate) fn oversized_source_with_a_shrinking_step(s: &mut TermStore) -> Hash {
    fn sum(s: &mut TermStore, lo: i64, hi: i64) -> Hash {
        if hi - lo == 1 {
            return s.lit(lo);
        }
        let mid = lo + (hi - lo) / 2;
        let (a, b) = (sum(s, lo, mid), sum(s, mid, hi));
        s.prim(crate::term::PrimOp::Add, a, b)
    }
    let big = sum(s, 0, crate::spec_check::MAX_NODES as i64);
    let big = s.abs(big);
    let n = s.var(1);
    let k = s.abs(n);
    let r = s.app(k, big);
    s.abs(r)
}

/// `\x. t_d`, `t_0 = x`, `t_{i+1} = t_i + t_i`: d + 2 distinct nodes, 2^(d+1)
/// as a tree, so its source text is exponentially long.
pub(crate) fn doubling(s: &mut TermStore, d: u32) -> Hash {
    let mut t = s.var(0);
    for _ in 0..d {
        t = s.prim(crate::term::PrimOp::Add, t, t);
    }
    s.abs(t)
}

// Shapes that unit tests in two or three files share, written as source.

/// `f` called at two arities, and nothing more: no single type fits it.
pub(crate) fn inconsistent_arity_parameter(s: &mut TermStore) -> Hash {
    source(s, r"\f. f 1 + f 1 2")
}

/// A parameter called at two arities, given a 2-ary literal; the live call
/// (`f 1 2`) saturates it.
pub(crate) fn inconsistent_arity_saturating_instance(s: &mut TermStore) -> Hash {
    source(s, r"(\f. if 0 < 1 then f 1 2 else f 1) (\a b. a + b)")
}

/// As `inconsistent_arity_saturating_instance`, but the live call is `f 1`
/// and the literal is 1-ary.
pub(crate) fn inconsistent_arity_under_applying_instance(s: &mut TermStore) -> Hash {
    source(s, r"(\f. if 1 < 0 then f 1 2 else f 1) (\a. a + 100)")
}

/// As `inconsistent_arity_saturating_instance`, with the literal capturing
/// the outer parameter `k`.
pub(crate) fn inconsistent_arity_capturing_instance(s: &mut TermStore) -> Hash {
    source(s, r"\k. (\f. if 0 < 1 then f 1 2 else f 1) (\a b. k + a + b)")
}

/// As `inconsistent_arity_saturating_instance`, with the literal chosen at
/// run time by an `if` on the outer parameter.
pub(crate) fn inconsistent_arity_runtime_chosen_instance(s: &mut TermStore) -> Hash {
    source(s, r"\pick. (\f. if 0 < 1 then f 1 2 else f 1) (if 0 < pick then (\a b. a + b) else (\a b. a - b))")
}

/// `iterate` with one dead call site (`g x 999`, behind `1 < 0`) that
/// makes `g` inconsistently classified. Bare; applied, it is
/// `inconsistent_arity_loop_carried_parameter_loop`.
pub(crate) fn inconsistent_arity_iterate(s: &mut TermStore) -> Hash {
    source(s, "rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)")
}

/// A loop that creates, in its self-call argument, a closure capturing its
/// closure-typed loop parameter `g`.
pub(crate) fn iterate_creating_a_closure_over_g(s: &mut TermStore) -> Hash {
    source(s, r"rec f n g x = if n <= 0 then x else f (n - 1) g (g x + (\y. g y + 1) x)")
}

/// `factorial` bound by `let` and called at 10: a self-recursive
/// combinator used as a value.
pub(crate) fn let_bound_factorial_10(s: &mut TermStore) -> Hash {
    source(s, "let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10")
}

/// A literal lambda whose body picks between two closures over `x`, applied
/// to `x`, its result passed to `\g. g 5`.
pub(crate) fn calls_a_capturing_closure_picked_by_if(s: &mut TermStore) -> Hash {
    source(s, r"\x. (\g. g 5) ((\x. if 0 < x then (\y. x + y) else (\y. x - y)) x)")
}

/// A self-recursive combinator partially applied (one argument of two) and
/// completed through `\g. g 1`.
pub(crate) fn a_pap_of_a_self_recursive_combinator(s: &mut TermStore) -> Hash {
    source(s, r"(\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc)) 3)")
}

/// As `a_pap_of_a_self_recursive_combinator`, with the combinator capturing
/// the outer parameter `z`.
pub(crate) fn a_pap_of_a_capturing_self_recursive_combinator(s: &mut TermStore) -> Hash {
    source(s, r"\z. (\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc + z)) 3)")
}

/// `over_application_if_between_closures` with its three arguments as
/// parameters.
pub(crate) fn over_application_if_between_closures_of_params(s: &mut TermStore) -> Hash {
    source(s, r"\p q r. (\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) p q r")
}
