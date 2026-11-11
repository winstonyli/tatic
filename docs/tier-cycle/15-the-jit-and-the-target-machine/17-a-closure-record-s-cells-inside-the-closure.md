### A closure record's cells inside the closure relation: a spike (2026-11-10)

The question: the other heap shape the survey missed. Can the closure relation itself say the record holds the
captured values, so callers that only pass a closure carry no layout? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-closure-relation-cells-spike.patch` (applies to `28975c2`, with the heap-state
patch inside); reverted. Runs took seconds and were not recorded through the wrapper.

**What changed.** A constructor `call_c` calls through a record pointer; the source side is `clo a v k`. The closure
relation is a statement hypothesis: if the continuation agrees once the record is handed back intact, the machine call
agrees with the source's `clo`. The record's invariant `Inv` is either concrete (`h (p + 8) = v`, A) or an abstract
statement binder (B), so a function that only passes the record cannot see the offset. Returns must hand the
invariant back (a framed return).

All four cases prove at n = 4, 8, 24, 64 (single runs, shared machine): the closure body (1.2 + 5.4 ms at n = 64),
`clo (clo y)` with abstract (1.7 + 4.2) and concrete (1.8 + 4.6) invariants, and an allocation then a call (6.7 +
9.2). The checker's n = 64 rerun gave 3.5 + 8.0 against 2.8 + 6.0, so "same cost" is plausible, not shown. Rejected:
a wrong captured value, a cell at the wrong offset, a wrong argument, a callee that writes the record (only the framed
return sees it), a wrong offset read, a wrong body, a store between calls (both shapes), one call against two.

What it settles, and what stays open:

- **Settled:** the closure relation can carry the record's invariant. With B, a pass-through function is proved once
  for every layout; it still carries one (abstract) invariant hypothesis, so the layout is hidden, not the hypothesis.
- **B cannot** store, allocate or read the record between calls (no frame rule for an abstract invariant); A can store
  if the stored value matches the source's. Neither handles a callee that mutates the record, several records, or
  term 27's type-indexed relation.
- **Open:** term 37's shape (a loop calling a closure each iteration) was not built; the per-function proofs were
  checked separately, not composed into one theorem, which is where an `Inv` universe problem would show.

