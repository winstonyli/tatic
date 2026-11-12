//! Mutations of an emitted body, for the gate's rejection tests.

use tatic_wasm::machine::Ins;

/// `code` with its first instruction (pre-order, into `If` arms and `Loop` bodies) that `f` maps replaced by `f`'s
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
                    Ins::Loop(b) => Ins::Loop(go(b, f, done)),
                    other => other.clone(),
                }
            })
            .collect()
    }
    go(code, f, &mut false)
}
