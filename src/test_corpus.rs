//! Two test terms `samples` can't hold: one with a free variable (the
//! parser rejects unbound names) and one built programmatically past
//! `spec_check::MAX_NODES`.

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
