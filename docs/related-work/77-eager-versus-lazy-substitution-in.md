## 77. Eager versus lazy substitution in kernels

Fetched 2026-09-30 (source files read through a summarising fetch; the two papers and the NbE line are abstract or search-result level only).

- **Lean 4 kernel**: `instantiate` skips by loose-bvar range and runs through `replace_rec_fn`, whose per-call cache is keyed by (pointer, offset) and used only for likely-shared nodes. Substitution is eager; beta instantiates the lambda body directly. The same memo was tried here and was slower on the lemma (bitvector design doc, section 20).
- **Rocq kernel** (`cClosure.mli`): lazy closures `FCLOS of constr * usubs`, `FLambda` keeping its body under an environment, and `Zupdate`/`FLOCKED` for sharing an evaluated result.
- **Gregoire and Leroy, "A compiled implementation of strong reduction" (ICFP 2002)**: bytecode abstract machine (from the ZAM) that weakly reduces open terms, plus a read-back procedure; "important speed-ups" over Coq's old reducer (abstract only).
- **Kleeblatt, "On a strongly normalizing STG machine with an application to dependent type checking" (TU Berlin, 2011)**: compiled normalisation inside a dependent type checker, "satisfying efficiency" (abstract only).
- **Abel, Coquand and Dybjer, NbE for Martin-Lof type theory (LICS 2007)**: environment-based evaluation then read back (search summary only).

- **Agda `Reduce.Fast`**: a call-by-need environment machine with an implicit heap (Hackage module doc, search-summary level).
- **smalltt** (Kovacs): NbE with closures and de Bruijn levels; its README reports elaboration 8 to 30 times faster than Agda on synthetic benchmarks and Church-numeral conversion at 0.712 s against 19.7 s for Agda (the author's own benchmarks, not reproduced here).
- **Rocq `cClosure.ml`**: a forced closure updates its mutable cell in place so later references share the result (`Zupdate`); `FLOCKED` marks a cell being updated.

What it means here. Lean's kernel is eager and fast, so eager substitution is not the flaw by itself; this lemma's O(n^2)-node bodies under O(n) betas are. Rocq's closure design is the one precedent for removing body construction inside a small kernel. The compiled routes put an untrusted code generator into checking, which this repo keeps apart on purpose. Options and a gate are in a 2026-09-30 options note, superseded by `docs/superpowers/specs/2026-10-02-search-execution-blend-design-part2.md` and deleted 2026-10-27 (`git show 6f877af:docs/superpowers/specs/2026-09-30-kernel-node-churn-options.md`).

