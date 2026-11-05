## 1. Where tatic's own kernel sits

`src/kernel.rs`'s own dependent-type kernel (`Sort`/`Pi`/`Id`/`W`, a
stratified predicative universe hierarchy, no impredicative encoding) is a
small fragment of the lambda cube's bottom-right corner — closer to
Martin-Löf Type Theory (MLTT) than to the Calculus of (Inductive)
Constructions (Coq's own core, which adds impredicative `Prop` and a
richer inductive-type mechanism) or to classical Church-style Higher-Order
Logic (HOL4/HOL Light/Isabelle/HOL, which stays simply-typed — no
dependent types at all, quantification over predicates/functions instead).

Pollack's "How to Believe a Machine-Checked Proof" (BRICS RS-97-18, 1997)
states the design this placement serves. Believe a proof by checking it
independently with a checker small enough to understand, preferably in
LCF style (a typed abstract type whose only constructors are the inference
rules), and then ask "what theorem is it": the formal statement and the
definitions it uses hereditarily must be read and accepted by a person,
because the checker only vouches for the derivation. tatic's trusted
checker is the `tatic-kernel` crate, which imports nothing from `tatic`
(`crates/tatic-kernel`), and the caveat that a proof is about `denote`, not
the emitted WAT (`docs/TOUR.md`), is the "what theorem is it" question.

This placement is *why* `prove_tail_recursive_universal` (`src/proof.rs`)
can't induct on a bare inductive `Nat` the way a CIC-based system would —
predicativity forbids the impredicative encoding that would let one
generic recursion principle cover every case, so it postulates a bespoke
`Ev(params, v)` family with its own postulated recursor mirroring
`kernel::WRec`'s universal-motive shape, by hand, per proof strategy. See
§3 below (guarded recursion) for the type-theoretic tool that would
actually solve this generically rather than ad hoc.

