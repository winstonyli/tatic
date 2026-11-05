## 81. Canonical forms for bitwise and mixed Boolean-arithmetic terms, and learning them (2026-10-22)

Asked because the joins' leftover laws need pure-bitwise identities (`and(x, and(y, x)) = and(x, y)`,
`xor(y, or(x, y)) = and(x, not y)`) and bridges (`or(x, y) - xor(x, y) = and(x, y)`), which the miner cannot propose
(`docs/tier-cycle/`, "Canonical forms: hand-coded or learned"). Fetched 2026-10-22: SiMBA (ar5iv HTML), GAMBA and
Ruler (abstract; Ruler's method from its ar5iv HTML), CoBRA (blog). From search summaries only, not read: MBA-Blast,
MBA-Solver, Enumo, Knuth's 4-input tables, null polynomials. From general knowledge, no source fetched: ANF and ROBDDs.

- **Pure bitwise.** Bitwise operators act on each bit alone, so a bitwise term over t atoms is fixed by its 2^t-row
  truth table. Canonical term forms: algebraic normal form (xor of ands; `or` becomes three monomials, up to 2^t in
  all), ROBDDs (canonical per variable order, not term-shaped), and a table of smallest formulas per function (Knuth
  enumerated minimum chains for 4 and 5 inputs). A smallest-formula table is canonical only with a fixed tie-break, and
  the smallest form of a composite is not built from its parts' smallest forms.
- **Linear MBA** (a sum of integer coefficients times bitwise functions of the variables, mod 2^n). SiMBA (Reichenwallner
  and Meerwald-Stadler, CheckMATE workshop at CCS 2022), Theorem 2: two linear MBAs are equal at width n if and only if
  they agree on the 2^t inputs in which each variable is 0 or 1. It solves for coefficients over the basis of conjunctions of the variables
  in order of their variable count, which never gets stuck; the paper calls the result "valid, but not necessarily
  optimal" and claims no uniqueness (it follows: the system is triangular with unit diagonal). Shifts are not discussed;
  `shl1` is 2x and so linear, `shr1` and `lt` are not.
- **Nonlinear MBA.** GAMBA (2023) extends SiMBA by algebraic rewriting and recovers the ground truth "in most cases", with
  no completeness claim. CoBRA (Trail of Bits, 2026): 36 passes over linear, semilinear, polynomial and mixed classes,
  72,960 of 73,066 benchmark expressions simplified; 106 "carry-sensitive mixed-domain" cases unsupported; each result
  checked on random 64-bit inputs or by Z3.
- **Polynomials mod 2^n** have canonical forms by null-polynomial reduction (Singmaster 1974), but cover add, sub, mul
  and shifts only; nothing combines them with bitwise operators canonically. They matter here only if `mul` arrives.
- **Learning the rules.** Ruler (Nandi et al., 2021) enumerates terms into an e-graph and gives each e-class a
  characteristic vector, its values on fixed inputs (operators act on vectors element-wise); classes with equal vectors
  give candidate rules. Its domains are booleans, 4- and 32-bit bit-vectors and rationals. Validation: exhaustive
  vectors are sound for booleans and bv4, Z3 for bv32, sampling for rationals. Enumo (Pal et al., OOPSLA 2023) makes the
  enumeration programmable.
- **Proofs.** None of the MBA tools emits a checkable proof; they test or call Z3. Here the kernel already proves both
  layers: `bitwise_law_k` (`crates/church-bv/src/rewrite.rs`) any pure-bitwise identity per bit, and `add_tree_law`
  (`crates/church-bv/src/machine.rs`) equal sum trees of add-free leaves by a carry encoding, up to `CARRY_CAP` carries.
  `pool_conjectures` (`machine.rs`) already groups a pool by its exhaustive values, Ruler's characteristic vector.

What it means here: the hand-coded option is SiMBA's form (conjunction-basis coefficients over the atoms); the learned one
is Ruler's grouping with the smallest member of each class as its representative, kernel-proved. The options and the
choice are in `docs/tier-cycle/`, "Canonical forms: hand-coded or learned".

