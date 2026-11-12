//! Goal 5's held-out rows: terms written without sight of the generator (T8). They must be `Accepted` by the gate and
//! install through the JIT; the freeze (T13) turned it on.
use super::*;
use crate::jit::compile::compile_specialised;
use crate::jit::shape::wasm_table;
use crate::jit::JitEngine;
use crate::proof::gate::{gate, Verdict};
use crate::testing::test_corpus as tc;

#[test]
fn held_out_terms_are_accepted() {
    for (name, build) in [("held_out_a", tc::held_out_a as fn(&mut TermStore) -> Hash), ("held_out_b", tc::held_out_b)] {
        let (v, installed) = std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn(move || {
                let mut s = TermStore::new();
                let h = build(&mut s);
                let c = compile_specialised(&s, h).expect("compiles");
                let v = match &c.specialised {
                    Some((s2, h2)) => gate(wasm_table(), s2, *h2, &c.frag),
                    None => gate(wasm_table(), &s, h, &c.frag),
                };
                let arity = crate::jit::shape::peel(&s, h).map_or(0, |p| p.0);
                let mut jit = JitEngine::new();
                let _ = jit.apply(&s, h, &vec![5; arity]);
                (v, jit.stats.compiled == 1)
            })
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(v, Verdict::Accepted, "{name}");
        assert!(installed, "{name} was not installed");
    }
}
