### Locals as a frame passed in, with and without the memory: a spike (2026-11-10)

The question: the state-shape survey recommended a frame of nested word pairs, read by `local.get` as a projection and
never passed back through a return, either keeping today's single memory component (l3) or dropping it (l2), and left
open how frames of different widths share one type. Throwaway, both arms on top of the modules and registry spikes;
patches `docs/superpowers/spikes/2026-11-10-frame-l3-spike.patch` and `-frame-l2-spike.patch` (each applies to
`343abc2` and carries its base); reverted.

Both arms build the frame as `V^M x V`, where M is the widest `arity + env + temps` in the module, every frame padded
with 0 to it. `local.get i` is a row whose operand projects the frame and `local.set i` rebuilds it; both reduce under
whnf because the frame is a concrete nested pair. `unpack` builds the callee's padded frame and has no `Pi R`; the
caller's frame comes back by closure in the call's continuation. l3 keeps the memory as one opaque argument
(`G A = Fr -> A -> Mem -> R`); l2 deletes it with `Store`, `Load` and `upd` (`G A = Fr -> A -> R`).

Every target and control of the base gives the same verdict in both arms: the sum loops, factorial,
`redundant_arithmetic_recursion`, fib, terms 13, 23 and 34 and the unseen terms prove at n = 4, 24 and 64 (term 23
newly at 64), the gen_real controls and the swapped two-callee pairings are rejected, and each arm's checker reran
the tests (gen_real 10 passed, tatic-wasm 37 passed, 4 ignored; runs `2026-11-10-chk-p1-l3`, `-chk-p1-l3-wasm`,
`-chk-p1-l2`, `-chk-p1-l2-real`). Padding worked for callees of different arity and environment, so no arm needed a
call row per callee.

| | base | l3 | l2 |
|---|---|---|---|
| `sim.rs` lines | 819 | 744 | 685 |
| walk rules in the generator | 5 | 4 | 4 |
| motive binders, the sum loop | 10 | 7 | (not counted) |
| build + check, direction only | 1 | about 0.5 (check, 3 alternating pairs) | about 0.4-0.5 (2.0x by the arm, 2.7x by its checker) |

The times come from a machine 53-96% busy with other sessions, untimed and uncounted, so only the direction holds (runs
`2026-11-10-l3-base-c` to `-f` against `-l3-b` to `-b3`, and `-l2-A1-real`, `-l2-A2-real` against `-l2-B3-real`;
the l3 arm's direct call 13 at n = 4 was slower than the base).

- **Settled:** locals need not live in the state. The frame deletes the stuck-slot rule, the slot hypotheses, the
  `untouched` clause, the locals and heap binders of the motive and the state's pair destructuring, in both arms; l2
  also deletes the memory with its rows (`trans` is left dead in l2). Padding to a module-wide width covers every real
  call shape tried.
- **Not deleted:** the recursion rule still reads the concrete frame's spine (a projection of a variable frame is stuck,
  with no eta), checks each parameter slot against the source argument and the padding against 0, and passes the
  temporaries to the induction hypothesis; `cont_rel`, `rel` and the numeral `d` stay; `Call` keeps its sort binders
  `S` and `A`, which index its result type (reasoned, not tried).
- **Costs of padding:** every law in a module mentions M, so a wider callee changes every function's statement, and the
  single-function gate's statement (width m) differs from the module's.
- **Open:** the memory is untested against heap writes in l3, since the generator still rejects `Store` and `Load`;
  both arms reason, untested, that the heap's return reopens a preserved-cells premise (l3: `Pres mu mu2` on `rel` and
  the callee law, with the other rules unchanged while `Mem` stays opaque; l2: the memory and its slot rule come back).

