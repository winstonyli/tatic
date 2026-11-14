//! The machine: programs as kernel data (docs/tier-cycle/, "Wasm programs as kernel data, kept"; option B of "Formalizing the target machine" there),
//! over a `Table` of rows (`wasm::table` is the wasm one).
//!
//! A program is a Church-encoded instruction tree typed by its start and end stacks,
//! `Prog S T = Pi F:(Sort2 -> Sort2). F T -> const -> word -> bit -> unary -> if -> call -> call_indirect -> set -> br -> F S` (one leaf
//! constructor per row class, in `ctor_list` order), where each
//! constructor takes the rest of the program (`const : Pi A. Op -> F (V,A) -> F A`, with the operand
//! `Op = Fr -> Pi R:Sort0. (V -> R) -> R` handing its word to a continuation; `word : Pi A. (V -> V -> V) ->
//! (V -> V -> Bv_1) -> F (V,A) -> F (V,V,A)` also takes the row's domain). Its meaning `M p R k` interprets `F A` as `Fr -> A -> Mem -> R` for an answer type `R : Sort0`: words are width-n Church vectors
//! (`encoding.rs`), stacks are nested `Sigma` pairs, the locals are a frame `Fr = V^fw x V` of nested word pairs
//! passed into every interpreter and on to the rest of the program (a `const`-class operand projects it; a
//! `set`-class operand rebuilds it with one slot replaced), memory is the opaque
//! `Mem = V -> (V -> R) -> R` that nothing reads, and an `if` chooses between its two continuations by its one-bit
//! condition (`choose`, as only the taken branch runs). A `word` site is guarded the same way: `choose(dom x y,
//! rest(op x y), z)`, with `z` the statement's out-of-fuel answer (`MeaningEnv::z`). Nothing is postulated.
use super::*;

/// `choose w x y = w (Lift R) (\c Y g. g (c R x y)) R id`, with `Lift R = Pi Y:Sort0. (R -> Y) -> Y`: a one-bit word
/// opens only at Sort1, and `Lift R` carries the Sort0 answer through it.
///
/// It is the application of the closed `choose_fn` to its four arguments, never an unfolded copy: the arguments (a branch
/// holds the rest of the program) are neither shifted under `choose`'s binders when built nor again when a conversion
/// reduces it, and the proof, which takes the real choice as its probe `CH`, then states the very term the statement
/// does, so the kernel's final comparison finds them equal without reducing a thing (a chain of `n` branches cost `n^2`
/// shifts when it unfolded them).
pub fn choose(r: Expr, w: Expr, x: Expr, y: Expr) -> Expr {
    apps(choose_fn(), vec![r, w, x, y])
}

/// `\R w x y. choose R w x y`, closed: the one definition of the choice.
pub fn choose_fn() -> Expr {
    Cx::default().lam(sort(0), |c, r| {
        c.lam(bv_ty(1), |c, w| {
            c.lam(c.at(r), |c, x| {
                c.lam(c.at(r), |c, y| {
                    let (r, w, x, y) = (c.at(r), c.at(w), c.at(x), c.at(y));
                    let lift = pi(sort(0), arrow(arrow(shift(&r, 0, 1), var(0)), var(0)));
                    let k = lam(bool0(), lam(sort(0), lam(arrow(shift(&r, 0, 2), var(0)),
                        app(var(0), app3(var(2), shift(&r, 0, 3), shift(&x, 0, 3), shift(&y, 0, 3))))));
                    apps(w, vec![lift, k, r, lam(r, var(0))])
                })
            })
        })
    })
}

/// An interpreter case's body from `A`, its operator if any, `rest`, the frame, the stack and the memory.
type Body<'a> = dyn Fn(&mut Cx, At, &[At], At, At, At, At) -> Expr + 'a;

/// What a stack slot holds: an n-bit word or a one-bit word (a compare's result).
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum K {
    W,
    B,
}

/// The shape of a row: its stack effect and the constructor class it is built through. `Const` is 0 to 1 with a word
/// result, `Word` 2 to 1 word-valued and guarded by its row's domain, `Bit` 2 to 1 bit-valued and unguarded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    Const,
    Word,
    Bit,
    /// Pops one word and writes it to a parameter slot of the frame (operand: the slot); pushes nothing.
    Set,
    /// Pops one word and pushes one word, unguarded (no domain, no operand): `wrap`, `extend`.
    Unary,
}

impl Class {
    /// How many words the row pops.
    pub fn pops(self) -> usize {
        match self {
            Class::Const => 0,
            Class::Set | Class::Unary => 1,
            Class::Word | Class::Bit => 2,
        }
    }
    /// What the row leaves on the stack, if anything.
    pub fn push(self) -> Option<K> {
        match self {
            Class::Const | Class::Word | Class::Unary => Some(K::W),
            Class::Bit => Some(K::B),
            Class::Set => None,
        }
    }
    /// Whether the row reads its operand (a constant or a slot); the others take 0.
    pub fn takes_operand(self) -> bool {
        matches!(self, Class::Const | Class::Set)
    }
}

/// One leaf instruction: its name, class, kernel meaning and printed line. `meaning(c, m, operand)` is the
/// constructor's operand: for `Const` a function of the frame that hands its word (a constant, or a projection of the
/// frame) to a continuation (`Machine::operand_ty`; a plain `Fr -> V` left the redex `op fr` in every stack value, and
/// conversion blew up), for `Set` the frame with the operand's slot replaced (`Machine::setter`), for `Word`/`Bit` the
/// closed circuit (`operand` is 0). `dom` is where the row has a value, read only at Word sites (`ops::Dom`).
#[derive(Clone, Copy)]
pub struct Row {
    pub name: &'static str,
    pub class: Class,
    pub meaning: fn(&mut Cx, &Machine, i64) -> Expr,
    pub dom: crate::ops::Dom,
    pub line: fn(i64) -> String,
}

/// A backend's leaf instructions, by name.
pub struct Table {
    rows: Vec<Row>,
}

impl Table {
    /// Panics on a duplicate name.
    pub fn new(rows: Vec<Row>) -> Table {
        for (i, r) in rows.iter().enumerate() {
            assert!(rows[..i].iter().all(|q| q.name != r.name), "duplicate row {:?}", r.name);
        }
        Table { rows }
    }
    pub fn row(&self, name: &str) -> Option<&Row> {
        self.rows.iter().find(|r| r.name == name)
    }
    /// The row names, in table order.
    pub fn names(&self) -> Vec<&'static str> {
        self.rows.iter().map(|r| r.name).collect()
    }
}

/// An instruction of a function body (spec 2026-11-08-v07-straight-line-gate-design.md, section 2).
/// `Raw` is a line the lowering emits that the machine does not model, so a body holding one is not well formed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ins {
    /// A table row; a 2-to-1 row carries operand 0.
    Row { name: &'static str, operand: i64 },
    If(Vec<Ins>, Vec<Ins>),
    /// `call`/`return_call` to the module position `j` (the printer picks by its tail rule; the JIT's lowering
    /// rewrites a tail call to the function's own position to the loop form, `Set`s then `Br`): pops the callee's
    /// arity in words, pushes one. Its meaning continues into the callee environment's entry `j`, then the rest.
    Call(usize),
    /// `call_indirect (type $ty{a})`, the field being the arity `a` (printed always as `call_indirect`, never the tail
    /// form): pops the index word, then `a` argument words, then the environment word, and pushes one word. Its meaning
    /// dispatches on the index over the module's dynamic set for the arity (`dynamic_set`); an index outside it answers
    /// `z`, as wasm traps on it.
    CallIndirect(usize),
    /// `br $top`: restart the function's own entry on the current frame with the activation's own return continuation.
    /// Typed like a `Call` with no arguments (pushes one word); its meaning ignores the stack under it and the code
    /// after it, which the printed function never reaches.
    Br,
    Raw(String),
}

/// How a function reaches its captures: `Params(k)` as its leading parameters `$e0 .. $e{k-1}`; `Pointer` through
/// `$env`, a pointer to its environment slots in linear memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnvAccess {
    Params(usize),
    Pointer,
}

/// A function of a module: its parameter count, how it reaches its captures, and its body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub arity: usize,
    pub env: EnvAccess,
    pub code: Vec<Ins>,
}

/// The shape check (trusted; the gate runs it before any statement exists): every record's body runs from `[]` to
/// `[word]`, holds no `Raw` and no unknown row, reads and writes (`local.get`, `local.set`) only slots below its own
/// record's arity, calls only
/// positions that have a record, no `call` reaches a `Pointer` record (it would have to push the environment first;
/// `CallIndirect` is how they are reached), and every record's env is `Params(0)` or `Pointer` (an env parameter
/// would shift the printed parameter slots off the frame's). `records` is by module position; `None` is scaffolding
/// with no body.
pub fn shape_check(table: &Table, records: &[Option<&Entry>]) -> Result<(), String> {
    let arities: Vec<Option<usize>> = records.iter().map(|r| r.map(|e| e.arity)).collect();
    fn gets(code: &[Ins], arity: usize) -> Result<(), String> {
        for ins in code {
            match ins {
                Ins::Row { name: name @ ("local.get" | "local.set"), operand }
                    if usize::try_from(*operand).map_or(true, |i| i >= arity) =>
                {
                    return Err(format!("{name} {operand} is out of the {arity} parameters"));
                }
                Ins::If(t, e) => {
                    gets(t, arity)?;
                    gets(e, arity)?
                }
                _ => {}
            }
        }
        Ok(())
    }
    for (pos, e) in records.iter().enumerate() {
        let Some(e) = e else { continue };
        // `Params(k)` with `k > 0` would shift the printed parameter slots off the frame's; `Pointer` prints `$env i32`
        // first and no modelled instruction reads it (D5)
        if let EnvAccess::Params(k @ 1..) = e.env {
            return Err(format!("position {pos}: env access Params({k}), not Params(0) or Pointer"));
        }
        let mut direct = None;
        visit_ins(&e.code, &mut |i| {
            if let Ins::Call(j) = i {
                if matches!(records.get(*j), Some(Some(Entry { env: EnvAccess::Pointer, .. }))) {
                    direct.get_or_insert(*j);
                }
            }
        });
        if let Some(j) = direct {
            return Err(format!("position {pos}: a direct call into a record reached through an environment pointer (position {j})"));
        }
        let end = shape(table, &e.code, vec![], &arities).map_err(|m| format!("position {pos}: {m}"))?;
        if end != vec![K::W] {
            return Err(format!("position {pos}: the body ends on {end:?}, not one word"));
        }
        gets(&e.code, e.arity).map_err(|m| format!("position {pos}: {m}"))?;
    }
    Ok(())
}

/// The one stack analysis: the stack after `code` from `st` (top first), or why the
/// code is ill formed. `arities[j]` is the number of words module position `j` pops (`None`: no such callee).
fn shape(table: &Table, code: &[Ins], mut st: Vec<K>, arities: &[Option<usize>]) -> Result<Vec<K>, String> {
    let pop = |st: &mut Vec<K>, want: &[K]| {
        if !st.starts_with(want) {
            return Err(format!("stack {st:?} lacks {want:?}"));
        }
        st.drain(..want.len());
        Ok(())
    };
    for ins in code {
        match ins {
            Ins::Row { name, operand } => {
                let Some(row) = table.row(name) else { return Err(format!("unknown row {name:?}")) };
                if !row.class.takes_operand() && *operand != 0 {
                    return Err(format!("row {name:?} takes no operand, got {operand}"));
                }
                pop(&mut st, &[K::W, K::W][..row.class.pops()])?;
                if let Some(k) = row.class.push() {
                    st.insert(0, k)
                }
            }
            Ins::If(t, e) => {
                // Printed as `if (result i64)`: each arm starts on an empty stack and leaves one word.
                pop(&mut st, &[K::B])?;
                for (arm, c) in [("then", t), ("else", e)] {
                    let out = shape(table, c, vec![], arities)?;
                    if out != [K::W] {
                        return Err(format!("the {arm} arm ends on {out:?}, not one word from an empty stack"));
                    }
                }
                st.insert(0, K::W)
            }
            // typed like a 0-argument `Call` (pushes one word); `br $top` never falls through, so the code after it is
            // dead in the printed function and its meaning ignores it
            Ins::Br => st.insert(0, K::W),
            Ins::Call(j) => {
                let Some(Some(n)) = arities.get(*j) else { return Err(format!("call to position {j}, which has no arity")) };
                pop(&mut st, &vec![K::W; *n])?;
                st.insert(0, K::W)
            }
            Ins::CallIndirect(a) => {
                pop(&mut st, &vec![K::W; *a + 2])?;
                st.insert(0, K::W)
            }
            Ins::Raw(s) => return Err(format!("raw line {s:?}")),
        }
    }
    Ok(st)
}

/// Calls `f` on every instruction of `code`, in order, recursing into the arms of an `If` after the `If` itself.
pub fn visit_ins(code: &[Ins], f: &mut dyn FnMut(&Ins)) {
    for i in code {
        f(i);
        if let Ins::If(t, e) = i {
            visit_ins(t, f);
            visit_ins(e, f)
        }
    }
}

/// The module's dynamic set for the arity `arity`: the positions `p` (ascending) whose record is reached through an
/// environment pointer and takes `arity` parameters, which are the only ones a closure call of that arity can enter
/// (a direct-only record is printed without `$env`, so its type is not `$ty{arity}` and wasm traps on the call). The one
/// place the set is defined.
pub fn dynamic_set(records: &[Option<&Entry>], arity: usize) -> Vec<usize> {
    let hit = |r: &Option<&Entry>| r.is_some_and(|e| e.env == EnvAccess::Pointer && e.arity == arity);
    records.iter().enumerate().filter(|(_, r)| hit(r)).map(|(p, _)| p).collect()
}

/// `dynamic_set` for every arity up to the largest record arity, indexed by arity.
pub fn dynamic_sets(records: &[Option<&Entry>]) -> Vec<Vec<usize>> {
    let widest = records.iter().flatten().map(|e| e.arity).max().unwrap_or(0);
    (0..=widest).map(|a| dynamic_set(records, a)).collect()
}

/// The positions entry `k`'s code calls other than `k` itself, sorted and distinct: its static `Call` targets and, for
/// each `CallIndirect(a)`, the dynamic set `dynamic[a]` (an arity past `dynamic` contributes nothing).
pub fn callees(k: usize, code: &[Ins], dynamic: &[Vec<usize>]) -> Vec<usize> {
    let mut out = vec![];
    visit_ins(code, &mut |i| match i {
        Ins::Call(j) => out.push(*j),
        Ins::CallIndirect(a) => out.extend(dynamic.get(*a).into_iter().flatten()),
        _ => {}
    });
    out.retain(|j| *j != k);
    out.sort_unstable();
    out.dedup();
    out
}

/// A dispatch chain folded from the right over `set`: `step(p1, step(p2, .. z))`, where `step(c, p, rest)` builds one
/// test-and-arm. The machine's meaning and the source's call both build their chain through it, so the order cannot drift.
pub fn dispatch_chain(c: &mut Cx, set: &[usize], z: Expr, step: &mut dyn FnMut(&mut Cx, usize, Expr) -> Expr) -> Expr {
    set.iter().rev().fold(z, |rest, p| step(c, *p, rest))
}

/// The stack after `code` from `st` (top first); panics on ill-formed code. `arities` as in `shape`.
pub fn out_stack(table: &Table, code: &[Ins], st: Vec<K>, arities: &[Option<usize>]) -> Vec<K> {
    shape(table, code, st, arities).unwrap_or_else(|e| panic!("{e}"))
}

/// Whether `code` from `st` is something the machine runs and falls through, or restarts at a `Br`: no `Raw`, no unknown row or operand on a
/// 2-to-1 row, no underflow, `if` arms that each leave one word from an empty stack, and each `Call(j)` to a position with an arity.
pub fn well_formed(table: &Table, code: &[Ins], st: &[K], arities: &[Option<usize>]) -> bool {
    shape(table, code, st.to_vec(), arities).is_ok()
}

mod prog;
pub use prog::*;

pub mod sim;
pub mod statement;

#[cfg(test)]
mod loop_tests;

#[cfg(test)]
mod tests {
    use super::*;

    /// `sty`'s one shift of the base gives the nested `prod`s' term, under binders and at both word widths.
    #[test]
    fn sty_is_the_nested_prods() {
        let t = crate::wasm::table();
        let w = Machine { n: 64, fw: 0, table: t };
        Cx::default().under(|c, base| {
            c.under(|c, _| {
                for ks in [vec![], vec![K::W], vec![K::B, K::W], vec![K::W, K::W, K::B, K::W, K::W]] {
                    let prods = ks.iter().rev().fold(c.at(base), |acc, k| prod(w.word(*k), acc));
                    assert!(prods == w.sty(c, &ks, base), "sty differs at {ks:?}");
                }
                sort(0)
            })
        });
    }

    #[test]
    fn well_formed_rejects_raw_underflow_and_mismatched_arms() {
        let t = crate::wasm::table();
        let cmp_if = |e: Vec<Ins>| vec![konst(1), konst(2), row("lt"), Ins::If(vec![konst(1)], e)];
        assert!(!well_formed(&t, &[Ins::Raw("x".into())], &[], &[]));
        assert!(!well_formed(&t, &[row("add")], &[], &[]));
        assert!(!well_formed(&t, &cmp_if(vec![]), &[], &[]));
        assert!(well_formed(&t, &cmp_if(vec![konst(2)]), &[], &[]));
    }

    /// A wasm `if (result i64)` arm starts on an empty stack and leaves one word, so an arm that reads the outer stack
    /// or leaves it as is would print text wasm rejects; the shape check holds arms to that rule.
    #[test]
    fn if_arms_start_empty_and_leave_one_word() {
        let t = crate::wasm::table();
        let under = |t_: Vec<Ins>, e: Vec<Ins>| vec![konst(7), konst(1), konst(2), row("lt"), Ins::If(t_, e)];
        assert!(!well_formed(&t, &under(vec![], vec![]), &[], &[]), "both arms leave the outer word");
        assert!(!well_formed(&t, &under(vec![konst(1), row("add")], vec![konst(1), row("add")]), &[], &[]), "arms read it");
        assert!(!well_formed(&t, &under(vec![konst(1), konst(2)], vec![konst(1), konst(2)]), &[], &[]), "two words");
        assert!(!well_formed(&t, &under(vec![konst(1), konst(2), row("lt")], vec![konst(3), konst(4), row("lt")]), &[], &[]), "a bit");
        let ok = under(vec![konst(1)], vec![konst(2)]);
        assert!(well_formed(&t, &ok, &[], &[]));
        assert_eq!(out_stack(&t, &ok, vec![], &[]), vec![K::W, K::W], "the outer word stays under the arm's");
    }

    pub(super) fn konst(v: i64) -> Ins {
        Ins::Row { name: "const", operand: v }
    }
    pub(super) fn row(name: &'static str) -> Ins {
        Ins::Row { name, operand: 0 }
    }

    #[test]
    fn well_formed_rejects_unknown_rows_and_operands_on_binary_rows() {
        let t = crate::wasm::table();
        assert!(!well_formed(&t, &[Ins::Row { name: "nope", operand: 0 }], &[], &[]));
        assert!(!well_formed(&t, &[konst(1), konst(2), Ins::Row { name: "add", operand: 7 }], &[], &[]));
        assert!(well_formed(&t, &[konst(1), konst(2), Ins::Row { name: "add", operand: 0 }], &[], &[]));
    }

    /// A `Call(j)` pops its callee's arity and pushes one word; a position without an arity is ill formed.
    #[test]
    fn call_pops_the_callees_arity_and_pushes_one_word() {
        let t = crate::wasm::table();
        let ar = [Some(2), None, Some(0)];
        assert!(well_formed(&t, &[konst(1), konst(2), Ins::Call(0)], &[], &ar));
        assert_eq!(out_stack(&t, &[konst(1), konst(2), Ins::Call(0)], vec![], &ar), vec![K::W]);
        assert!(well_formed(&t, &[Ins::Call(2)], &[], &ar));
        assert!(!well_formed(&t, &[konst(1), Ins::Call(0)], &[], &ar), "underflow");
        assert!(!well_formed(&t, &[Ins::Call(1)], &[], &ar), "no arity");
        assert!(!well_formed(&t, &[Ins::Call(3)], &[], &ar), "no such position");
        assert!(!well_formed(&t, &[Ins::Call(2)], &[], &[]), "no table of arities");
    }

    /// `[local.get 1, local.get 0, sub]` over the frame `(a, (b))` answers `sub b a` by `refl`, and not `sub a b`: the
    /// slots and the operand order are observable. Slot 2 of a width-2 frame is out of range.
    #[test]
    fn local_get_reads_the_frame() {
        let t = crate::wasm::table();
        let w = Machine { n: 8, fw: 2, table: t };
        let n = w.n;
        let get = |i| Ins::Row { name: "local.get", operand: i };
        let code = [get(1), get(0), row("sub")];
        // S R k a b s mu Z
        let law_for = |b_minus_a: bool| {
            let tys: Vec<Ty> = vec![
                ty!(|_c, _x| sort(2)),
                ty!(|_c, _x| sort(0)),
                ty!(|c, x| { let t = w.sty(c, &[K::W], x[0]); w.g(c, x[1], t) }),
                ty!(|_c, _x| bv_ty(n)),
                ty!(|_c, _x| bv_ty(n)),
                ty!(|c, x| c.at(x[0])),
                ty!(|c, x| w.mem(c, x[1])),
                ty!(|c, x| c.at(x[1])),
            ];
            law(&tys, |c, x| {
                let p = w.prog(c, &code, &[], x[0], &[]);
                let p = c.mark(p);
                // the environment of no functions: a call answers 0 at the memory it was given
                let r = x[1];
                let none = c.lam(w.v(), |c, _j| {
                    c.lam(w.fr(), |c, _fr| {
                        let mem = w.mem(c, r);
                        c.lam(mem, |c, mu| {
                            let ret = arrow(w.v(), arrow(w.mem(c, r), c.at(r)));
                            c.lam(ret, |c, k| app2(c.at(k), lit(n, 0), c.at(mu)))
                        })
                    })
                });
                let none = c.mark(none);
                let fr = w.frame(&[c.at(x[3]), c.at(x[4])]);
                // no `Br` here; `R` is abstract, so `restart` is built from the continuation
                let restart = c.lam(w.fr(), |c, fr2| {
                    let mem = w.mem(c, r);
                    c.lam(mem, |c, mu2| app3(c.at(x[2]), c.at(fr2), mkpair(c.at(x[0]), lit(n, 0), c.at(x[5])), c.at(mu2)))
                });
                let restart = c.mark(restart);
                let me = MeaningEnv { r, ch: None, z: x[7], calls: none, restart, dynamic: &[] };
                let l = app3(w.meaning(c, p, x[2], &me), fr, c.at(x[5]), c.at(x[6]));
                let (p, q) = if b_minus_a { (x[4], x[3]) } else { (x[3], x[4]) };
                let val = app2(sub(n), c.at(p), c.at(q));
                (refl(l), id(c.at(x[1]), l, app3(c.at(x[2]), fr, mkpair(c.at(x[0]), val, c.at(x[5])), c.at(x[6]))))
            })
        };
        tatic_kernel::scoped(|| {
            let (p, s) = law_for(true);
            ck("local.get 1, local.get 0, sub = sub b a", &p, &s);
            let (p, s) = law_for(false);
            assert!(holds(&p, &s).is_err(), "sub a b must be rejected");
        });
        let out_of_range = std::panic::catch_unwind(|| {
            let t = crate::wasm::table();
            let w = Machine { n: 8, fw: 2, table: t };
            Cx::default().under(|c, base| {
                w.prog(c, &[Ins::Row { name: "local.get", operand: 2 }], &[], base, &[]);
                sort(0)
            })
        });
        let msg = out_of_range.expect_err("local.get 2 at fw 2 must panic");
        let msg = msg.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(msg.contains("out of the frame's width"), "{msg}");
    }

    /// O1 (the spec's operand-free `[unpack, idx, rest]`) is not expressible: the call's result is `F S`, `S` the
    /// arity-dependent input stack, and the kernel has no implicit arguments, so `S` and `A` stay explicit binders
    /// (D3's fallback). A call of any arity types as one constructor, `Pi A S. (S -> Fr x A) -> V -> F (V, A) -> F S`.
    #[test]
    fn call_constructor_types_with_sort_binders() {
        let t = crate::wasm::table();
        let w = Machine { n: 8, fw: 3, table: t };
        let ar = [Some(1), Some(2), Some(3)];
        let calls: [(&str, Vec<Ins>); 3] = [
            ("one argument", vec![konst(1), Ins::Call(0)]),
            ("two arguments", vec![konst(1), konst(2), Ins::Call(1)]),
            ("three arguments", vec![konst(1), konst(2), konst(3), Ins::Call(2)]),
        ];
        let want = w.code_ty(&mut Cx::default(), K::W);
        for (name, code) in calls {
            let p = Cx::default().lam(sort(2), |c, base| w.prog(c, &code, &[], base, &ar));
            let got = infer(&Ctx::new(), &p).unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(def_eq(&got, &want), "{name}: not a program from [] to [word]");
        }
    }

    /// `frame([x])` at `fw` 3 is `(x, (0, (0, 0)))`: padded with zeros and a terminal zero word.
    #[test]
    fn frame_pads_with_zeros() {
        let t = crate::wasm::table();
        let w = Machine { n: 8, fw: 3, table: t };
        let z = lit(8, 0);
        let xv = lit(8, 5);
        let want = mkpair(w.words(2, w.v()), xv, mkpair(w.words(1, w.v()), z, mkpair(w.words(0, w.v()), z, z)));
        assert!(def_eq(&w.frame(&[xv]), &want), "frame([x]) is not (x, (0, (0, 0)))");
        assert!(def_eq(&infer(&Ctx::new(), &w.frame(&[xv])).unwrap(), &w.fr()), "frame has the type Fr");
    }
}
