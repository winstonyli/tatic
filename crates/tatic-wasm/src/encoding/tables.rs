use super::*;

/// Closed `Pi v_0..v_(k-1). GoodBool v_0 -> .. -> GoodBool v_(k-1) -> body(v)`, by case analysis on all `k`
/// bits; `leaf(values)` proves `body(literal bits)`. Every node's motive applies one closed `P = \v. body(v)`, so the
/// kernel types `body` once rather than at each of the 2^k - 1 nodes (docs/tier-cycle/, "One motive for a case tree").
pub fn lemma_n(k: usize, body: &dyn Fn(&[Expr]) -> Expr, leaf: &dyn Fn(&[bool]) -> Expr) -> (Expr, Expr) {
    fn elim(k: usize, p: &Expr, leaf: &dyn Fn(&[bool]) -> Expr, vals: &mut Vec<Option<bool>>) -> Expr {
        let Some(j) = vals.iter().position(|v| v.is_none()) else {
            return leaf(&vals.iter().map(|v| v.unwrap()).collect::<Vec<_>>());
        };
        // inside the motive binder, v_m is var(2k - m) (shifted once)
        let args: Vec<Expr> = (0..k)
            .map(|m| if m == j { var(0) } else { vals[m].map_or_else(|| var((2 * k - m) as u32), bit) })
            .collect();
        let motive = lam(bool0(), apps(*p, args));
        vals[j] = Some(true);
        let on_true = elim(k, p, leaf, vals);
        vals[j] = Some(false);
        let on_false = elim(k, p, leaf, vals);
        vals[j] = None;
        app3(var((k - 1 - j) as u32), motive, on_true, on_false)
    }
    let mut p = body(&(0..k).map(|m| var((k - 1 - m) as u32)).collect::<Vec<_>>());
    for _ in 0..k {
        p = lam(bool0(), p);
    }
    let mut proof = elim(k, &p, leaf, &mut vec![None; k]);
    for _ in 0..k {
        proof = lam(app(good_bool(), var(k as u32 - 1)), proof);
    }
    for _ in 0..k {
        proof = lam(bool0(), proof);
    }
    (proof, lemma_n_ty(k, body))
}

/// `lemma_n`'s statement alone: `Pi v_0..v_(k-1). GoodBool v_0 -> .. -> GoodBool v_(k-1) -> body(v)`.
pub fn lemma_n_ty(k: usize, body: &dyn Fn(&[Expr]) -> Expr) -> Expr {
    let mut ty = body(&(0..k).map(|m| var((2 * k - 1 - m) as u32)).collect::<Vec<_>>());
    for _ in 0..k {
        ty = pi(app(good_bool(), var(k as u32 - 1)), ty);
    }
    for _ in 0..k {
        ty = pi(bool0(), ty);
    }
    ty
}

/// The reduced ordered decision diagram of a truth table over `nv` variables: nodes `(level, hi, lo)` with ids from 2
/// (0 is false, 1 is true), and the root id. A node whose two children coincide is skipped.
pub struct TabBdd {
    pub nodes: Vec<(usize, usize, usize)>,
    pub root: usize,
}

pub fn tab_bdd(nv: usize, tab: &dyn Fn(&[bool]) -> bool) -> TabBdd {
    fn go(nv: usize, tab: &dyn Fn(&[bool]) -> bool, fixed: &mut Vec<bool>, nodes: &mut Vec<(usize, usize, usize)>, unique: &mut hashbrown::HashMap<(usize, usize, usize), usize>) -> usize {
        if fixed.len() == nv {
            return tab(fixed) as usize;
        }
        let level = fixed.len();
        fixed.push(true);
        let hi = go(nv, tab, fixed, nodes, unique);
        fixed.pop();
        fixed.push(false);
        let lo = go(nv, tab, fixed, nodes, unique);
        fixed.pop();
        if hi == lo {
            return hi;
        }
        *unique.entry((level, hi, lo)).or_insert_with(|| {
            nodes.push((level, hi, lo));
            nodes.len() + 1
        })
    }
    let mut nodes = vec![];
    let root = go(nv, tab, &mut vec![], &mut nodes, &mut Default::default());
    TabBdd { nodes, root }
}

/// A truth table over `vars` as a closed lambda applied to them (so large argument expressions are not duplicated
/// once per row), whose body is the table's reduced decision diagram as nested `mux`es. The closed lambda is built once per
/// truth table (`gen_memo`): a case tree states the same tables at every leaf.
pub fn table_app(vars: &[Expr], tab: &dyn Fn(&[bool]) -> bool) -> Expr {
    thread_local! {
        static BODIES: GenMemo<Vec<bool>, Expr> = Default::default();
    }
    let k = vars.len();
    // rows in `index_of` order (first variable most significant)
    let mut b = vec![false; k];
    let rows: Vec<bool> = (0..1usize << k)
        .map(|i| {
            for (j, x) in b.iter_mut().enumerate() {
                *x = i >> (k - 1 - j) & 1 == 1;
            }
            tab(&b)
        })
        .collect();
    let body = gen_memo(&BODIES, rows, |rows| {
        let d = tab_bdd(k, &|b| rows[b.iter().fold(0, |a, x| a * 2 + *x as usize)]);
        let bv: Vec<Expr> = (0..k).map(|i| var((k - 1 - i) as u32)).collect();
        let mut exprs: Vec<Expr> = vec![f(), t()];
        for &(level, hi, lo) in &d.nodes {
            exprs.push(mux(bv[level], exprs[hi], exprs[lo]));
        }
        let mut body = exprs[d.root];
        for _ in 0..k {
            body = lam(bool0(), body);
        }
        body
    });
    apps(body, vars.to_vec())
}

/// The Shannon expansion of a truth table over `vars`.
pub fn table_expr(vars: &[Expr], tab: &dyn Fn(&[bool]) -> bool) -> Expr {
    fn go(vars: &[Expr], tab: &dyn Fn(&[bool]) -> bool, fixed: &mut Vec<bool>) -> Expr {
        if fixed.len() == vars.len() {
            return bit(tab(fixed));
        }
        let c = vars[fixed.len()];
        fixed.push(true);
        let hi = go(vars, tab, fixed);
        fixed.pop();
        fixed.push(false);
        let lo = go(vars, tab, fixed);
        fixed.pop();
        mux(c, hi, lo)
    }
    go(vars, tab, &mut vec![])
}

pub fn sum3(a: Expr, b: Expr, c: Expr) -> Expr {
    xor(xor(a, b), c)
}
pub fn maj(a: Expr, b: Expr, c: Expr) -> Expr {
    or(and(a, b), and(c, xor(a, b)))
}
/// Table over `[a, b, z, p, q]` (state total `p + 2q`): the output bit (0), the next `p` (1) or next `q` (2).
pub fn assoc_table(which: usize, v: &[bool]) -> bool {
    let m = v[0] as u32 + v[1] as u32 + v[2] as u32 + v[3] as u32 + 2 * v[4] as u32;
    let next = m / 2;
    match which {
        0 => m % 2 == 1,
        1 => next % 2 == 1,
        _ => next >= 2,
    }
}
/// The left or right side's output bit (0), next `xor` (1) or next `and` (2) of its two carries, from `[a, b, z, c, d]`
/// (for the right side `c`, `d` are its `e`, `f`).
pub fn assoc_side(left: bool, which: usize, v: &[Expr]) -> Expr {
    let (a, b, z, c, d) = (v[0], v[1], v[2], v[3], v[4]);
    let (out, c2, d2) = if left {
        let s = sum3(a, b, c);
        (sum3(s, z, d), maj(a, b, c), maj(s, z, d))
    } else {
        let t = sum3(b, z, c);
        (sum3(a, t, d), maj(b, z, c), maj(a, t, d))
    };
    match which {
        0 => out,
        1 => xor(c2, d2),
        _ => and(c2, d2),
    }
}
/// `G_which(a, b, z, p, q)`.
pub fn assoc_g(which: usize, v: &[Expr]) -> Expr {
    table_expr(v, &|bits| assoc_table(which, bits))
}

/// A `Bool0` expression with its `GoodBool` witness.
#[derive(Clone)]
pub struct Gb {
    pub e: Expr,
    pub g: Expr,
}
pub struct GoodOps {
    pub and: Expr,
    pub or: Expr,
    pub xor: Expr,
}
impl GoodOps {
    pub fn new() -> GoodOps {
        GoodOps {
            and: good2(&|a, b| and(a, b), &and_truth).0,
            or: good2(&|a, b| or(a, b), &or_truth).0,
            xor: good2(&|a, b| xor(a, b), &xor_truth).0,
        }
    }
    pub fn go(&self, w: &Expr, e: Expr, x: &Gb, y: &Gb) -> Gb {
        Gb { g: apps(*w, vec![x.e, y.e, x.g, y.g]), e }
    }
    pub fn and(&self, x: &Gb, y: &Gb) -> Gb {
        self.go(&self.and, and(x.e, y.e), x, y)
    }
    pub fn or(&self, x: &Gb, y: &Gb) -> Gb {
        self.go(&self.or, or(x.e, y.e), x, y)
    }
    pub fn xor(&self, x: &Gb, y: &Gb) -> Gb {
        self.go(&self.xor, xor(x.e, y.e), x, y)
    }
    pub fn sum3(&self, a: &Gb, b: &Gb, c: &Gb) -> Gb {
        let ab = self.xor(a, b);
        self.xor(&ab, c)
    }
    pub fn maj(&self, a: &Gb, b: &Gb, c: &Gb) -> Gb {
        let (ab, x) = (self.and(a, b), self.xor(a, b));
        let cx = self.and(c, &x);
        self.or(&ab, &cx)
    }
}

