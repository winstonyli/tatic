### The partial row's cost, and gcd through the generator (2026-11-10)

The question: the decision file picks a partial row for remainder (outside its domain the machine answers the
no-value answer `z`). What does the guard cost, and does gcd then install? Throwaway; patches
`docs/superpowers/spikes/2026-11-10-partial-row-spike.patch` (the rem-cost probe plus the row; applies to `b092e5c`)
and `docs/superpowers/spikes/2026-11-10-partial-row-gcd-spike.patch` (combined with the generator-on-real-terms
patch); reverted.

**What changed.** `Dom::NonZeroDivisor` has `holds(x, y)` and a kernel circuit; `shape::dom_of` is the one lookup,
read by `eval::apply_prim` (its two hand-written zero checks go), `Source::cps` and the machine. A partial row is a new
constructor, `bin` plus the domain, meaning `choose(r, dom x y, rest (op x y), z)`. The generator gained one general
rule: two sides that are the same stuck term are equal by `refl` (both answer `z` outside the domain). `eval` now
reads `jit::shape`, so the lookup belongs in `lang`.

Cost, runs `2026-11-10-i4-partial-row-cost` and `-cost-2` (untimed, 59-66% load), build + check at n = 64 in ms,
guarded against unguarded: rem in tail position 20.1 and 27.3 against 25.7 and 30.0; non-tail `(a % b) + b` 24.4
and 20.9 against 25.2 and 25.8; `(a % b) % c` 28.4 and 32.5 against 22.3 and 31.0; rem in an arm 30.0 and 36.2
against 25.8 and 35.3. At n = 64 the guard is inside the spread between samples (up to about 40%); at n = 4 the
guarded rows are higher in all 8 pairs (under 1 ms), and at n = 24 one pair is 58% higher (4.6 against 2.9 ms).

gcd (`if b == 0 then a else f b (a % b)`) installs through the generator from its real term, run
`2026-11-10-i4-partial-row-gcd-4`: 18.0 + 24.1 ms at n = 64; the two-base-case gcd 12.1 + 22.6 ms. Rejected: the
machine dropping the guard ("the machine recurses but the source branches"), the machine alone testing the wrong
operand, and rem replaced by mul or sub. Accepted, as the decision file predicts: the wrong operand on both sides,
and no guard on either; only the table test can see those (reasoning: the domain circuit then differs from `holds` at
(5, 0); the table test was not run with these mutants). The table test at b = 0 (`-table`) passes: the domain circuit
equals `holds`, eval errors and wasmtime traps exactly where `holds` is false, and where defined the three agree,
`MIN % -1` giving 0 in all.

