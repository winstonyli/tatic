## 75. Relational compilation (Rupicola) as the shape of "found to be equivalent"

Read on 2026-09-30 from Pit-Claudel's thesis page and the Rupicola README; the PLDI 2022 PDF could not be text-extracted here, so anything below marked "not stated" was absent from those pages, not from the paper.

What it does. Compiling a functional program `s` is recast as proving `exists t, t ~ s` for a low-level program `t`, so the result carries its own correctness proof (the thesis's wording: "correct-by-construction"). The search unifies the goal against the conclusions of compilation lemmas held in a hint database, each lemma's premises becoming subgoals, with priorities on the hints. The thesis page shows the shape on a circuit compiler, not on Rupicola itself: `Op "add" [c1; c2] ~ Z.add g1 g2` from `c1 ~ g1` and `c2 ~ g2`, plus a premise that the operator's semantics is `Z.add`.

Loops. "Each type of loop is compiled [by] a custom lemma": separate lemmas for maps, folds and range iteration. The thesis states that invariant inference is then automatic, because each lemma expresses the intermediate state through the corresponding high-level iterator rather than through low-level primitives. Not stated on the pages read: the lemma statements themselves, the trusted base, and any timings.

What it means here.
- tatic's universal tail-recursion theorem (`loop_val(params, v, e) = v` over an `Ev` derivation) is already a per-loop-shape lemma whose invariant is stated on the high-level side. Rupicola's design says to add a shape by adding a lemma, not by changing the compiler.
- `specialise.rs` plus `spec_check.rs` already has the architecture: an untrusted search emits a trace, and a small checker replays it. A rewrite-lemma database would add steps to that trace that are checked by the kernel rather than certificate-checked (§37).
- Rupicola is deliberately incomplete: it produces good code where an expert supplied lemmas. The same stance fits a JIT whose fallback is the interpreter.
- Design sketch: `docs/superpowers/specs/2026-09-30-bitvector-interface-design.md`, section 10.

