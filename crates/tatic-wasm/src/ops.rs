//! The operator table: each wasm `i64` operator the machine runs, with its kernel term, its result kind and its WAT
//! mnemonic (spec 2026-11-08-v07-straight-line-gate-design.md, section 4). The lowering prints the mnemonic and the
//! machine runs the term, so this table is the one place the two meet; `op_rows_are_closed_and_typed` and tatic's
//! table check guard it.
use super::*;
use wasm::K;

/// A wasm `i64` binary operator. `LtU` has no source op; it serves the `LtS`-for-`LtU` control only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    LtS,
    LeS,
    Eq,
    LtU,
}

impl Op {
    /// The closed `V -> V -> V` (word rows) or `V -> V -> Bv_1` (bit rows) circuit at width `n`, built once per width
    /// and generation (`constant_n`).
    pub fn term(self, n: usize) -> Expr {
        let build: fn(usize) -> Expr = match self {
            Op::Add => add,
            Op::Sub => sub,
            Op::Mul => mul,
            Op::LtS => lt_s,
            Op::LeS => le_s,
            Op::Eq => eq_bit,
            Op::LtU => lt_u,
        };
        constant_n(build, n)
    }
    pub fn mnemonic(self) -> &'static str {
        match self {
            Op::Add => "i64.add",
            Op::Sub => "i64.sub",
            Op::Mul => "i64.mul",
            Op::LtS => "i64.lt_s",
            Op::LeS => "i64.le_s",
            Op::Eq => "i64.eq",
            Op::LtU => "i64.lt_u",
        }
    }
    /// What the operator leaves on the stack: a word, or a compare's one-bit word.
    pub fn kind(self) -> K {
        match self {
            Op::Add | Op::Sub | Op::Mul => K::W,
            Op::LtS | Op::LeS | Op::Eq | Op::LtU => K::B,
        }
    }
}

#[test]
fn op_rows_are_closed_and_typed() {
    let n = 8;
    let v = bv_ty(n);
    for o in [Op::Add, Op::Sub, Op::Mul, Op::LtS, Op::LeS, Op::Eq, Op::LtU] {
        let want = match o.kind() {
            K::W => arrow(v.clone(), arrow(v.clone(), v.clone())),
            K::B => arrow(v.clone(), arrow(v.clone(), bv_ty(1))),
        };
        let got = infer(&Ctx::new(), &o.term(n)).unwrap_or_else(|e| panic!("{o:?}: {e}"));
        assert!(def_eq(&got, &want), "{o:?} ({}) has the wrong type", o.mnemonic());
    }
}
