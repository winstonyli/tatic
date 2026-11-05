## 5. Self-types / Cedille — the same "postulate your way to power" tradeoff, one level down

Cedille (Stump et al.) gets inductive-datatype- and dependent-type-*like*
expressiveness on top of a base far weaker than full CIC (System Fω plus
one new "self type" former, `ιx:A. B`) rather than deriving it from a
maximal dependent kernel. This is the same tradeoff axis tatic itself
sits on — `assume_prim_fact`/`call_eq_ref`/every other computation-rule
axiom in `src/proof.rs` postulates exactly the behavior needed and no
more, rather than deriving it from first principles — just applied one
level up (type formers) instead of at the term/axiom level.

