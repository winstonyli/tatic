//! Mutations of an emitted body, for the gate's rejection tests.

use tatic_wasm::machine::Ins;

/// `code` with its first instruction (pre-order, into `If` arms) that `f` maps replaced by `f`'s
/// answer; unchanged when nothing matches.
pub(crate) fn mutate(code: &[Ins], f: &dyn Fn(&Ins) -> Option<Ins>) -> Vec<Ins> {
    fn go(code: &[Ins], f: &dyn Fn(&Ins) -> Option<Ins>, done: &mut bool) -> Vec<Ins> {
        code.iter()
            .map(|ins| {
                if *done {
                    return ins.clone();
                }
                if let Some(r) = f(ins) {
                    *done = true;
                    return r;
                }
                match ins {
                    Ins::If(t, e) => {
                        let t = go(t, f, done);
                        Ins::If(t, go(e, f, done))
                    }
                    other => other.clone(),
                }
            })
            .collect()
    }
    go(code, f, &mut false)
}

/// `frag` with its entry function's record replaced by `f` of it (the printed text is derived from the records, so this
/// is the module the mutated list would print).
pub(crate) fn with_entry(
    mut frag: crate::jit::compile::CompiledFragment,
    f: impl FnOnce(tatic_wasm::machine::Entry) -> tatic_wasm::machine::Entry,
) -> crate::jit::compile::CompiledFragment {
    use crate::jit::compile::Item;
    let pos = frag.entry_pos;
    let mut f = Some(f);
    for item in &mut frag.module {
        if let Item::Func { pos: p, entry } = item {
            if *p == pos {
                *entry = (f.take().expect("one entry record"))(entry.clone());
            }
        }
    }
    assert!(f.is_none(), "the module has no entry record");
    frag
}

/// The instruction ranges of the `arity` arguments a call at the end of `before` takes, in argument order: each range
/// is the shortest suffix that leaves one more word on the stack than it found (`Call(j)` pops `arity` words, a row its
/// class's pops, and every instruction here pushes one).
fn arg_ranges(before: &[Ins], arity: usize, table: &tatic_wasm::machine::Table) -> Vec<std::ops::Range<usize>> {
    let mut out = vec![];
    let mut end = before.len();
    for _ in 0..arity {
        let (mut start, mut need) = (end, 1i64);
        while need > 0 {
            start -= 1;
            let pops = match &before[start] {
                Ins::Row { name, .. } => table.row(name).expect("a table row").class.pops(),
                Ins::Call(_) => arity,
                other => panic!("{other:?} inside a call's argument"),
            };
            need += pops as i64 - 1;
        }
        out.push(start..end);
        end = start;
    }
    out.reverse();
    out
}

/// How many `Call(pos)` instructions `code` holds, nested ones included.
pub(crate) fn count_call_sites(code: &[Ins], pos: usize) -> usize {
    code.iter()
        .map(|i| match i {
            Ins::Call(p) => usize::from(*p == pos),
            Ins::If(t, e) => count_call_sites(t, pos) + count_call_sites(e, pos),
            _ => 0,
        })
        .sum()
}

/// `code` with its `site`-th `Call(pos)` (pre-order, into `If` arms) edited by `edit`, which is handed the block holding
/// the call, the call's index in it and the ranges of its `arity` arguments before it, and changes the block in place.
pub(crate) fn edit_call_site(
    code: &[Ins],
    site: usize,
    pos: usize,
    arity: usize,
    table: &tatic_wasm::machine::Table,
    edit: &dyn Fn(&mut Vec<Ins>, usize, &[std::ops::Range<usize>]),
) -> Vec<Ins> {
    fn go(
        block: &[Ins],
        seen: &mut usize,
        site: usize,
        pos: usize,
        arity: usize,
        table: &tatic_wasm::machine::Table,
        edit: &dyn Fn(&mut Vec<Ins>, usize, &[std::ops::Range<usize>]),
    ) -> Vec<Ins> {
        let mut out = block.to_vec();
        for (i, ins) in block.iter().enumerate() {
            match ins {
                Ins::Call(p) if *p == pos => {
                    if *seen == site {
                        let args = arg_ranges(&block[..i], arity, table);
                        edit(&mut out, i, &args);
                        *seen += 1;
                        return out;
                    }
                    *seen += 1;
                }
                Ins::If(t, e) => {
                    let t = go(t, seen, site, pos, arity, table, edit);
                    out[i] = Ins::If(t, go(e, seen, site, pos, arity, table, edit));
                }
                _ => {}
            }
        }
        out
    }
    go(code, &mut 0, site, pos, arity, table, edit)
}
