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
