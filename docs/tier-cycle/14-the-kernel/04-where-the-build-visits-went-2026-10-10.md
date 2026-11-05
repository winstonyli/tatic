### Where the build visits went (2026-10-10)
An attribution prototype (reverted; per-call-site counters around the builders, parameters off) found the build visits were almost
all the kernel's `shift`, called by the proof builders themselves rather than by kernel checks. On cmp3d (69M): `lemma_n` 42.7M (its
motive and its leaf, about half each), `lemma_dd` 12.5M, other shifts 7.3M, `add_tree_law` 2.7M, `raw_table` normalisation 1.9M,
`nf_whnf` 1.1M. The source was `bool0()` (`Pi C. C -> C -> C`): written with `arrow`, which shifts its codomain, and `and`/`or`/`xor`
rebuild it at every call, millions of times while building the case-tree motives. `bool0` is now written with explicit `pi`s, which
removes the shift and leaves the term identical (per-law M, nodes and check visits unchanged). With parameters off, build visits
fell from 8.6M to 2.0M (sbo3) and from 69M to 17.3M (cmp3d).

The rest of cmp3d's builder cost is mostly `lemma_dd` (11.0M): `cong_n` and `trans_proof` shift the J motive at every node of a
decision diagram. Parked: removing it needs a different proof shape (for example a closed `cong_mux` lemma used as a parameter), and
these shifts are cheap in time (below), so it would change the visit count more than the run time. Moot since 2026-10-13: the
diagram path is deleted ("Decision diagrams deleted").

Kernel work with parameters as the only path and the new `bool0` (same 300-law windows; M and law-check visits identical to the
"on" columns above):

| family, library | M | law-check visits (M) | build visits (M), before / after `bool0` | total (M), before / after |
|---|---|---|---|---|
| sbo3, none | 92 | 2.5 | 22.9 / 8.2 | 25.3 / 10.6 |
| sbo3, own | 17 | 1.2 | 11.5 / 4.9 | 12.7 / 6.1 |
| cmp3d, none | 118 | 4.8 | 99.0 / 32.8 | 103.9 / 37.7 |
| cmp3d, own | 31 | 3.1 | 103.8 / 52.0 | 106.9 / 55.1 |

- **Total kernel work and M now disagree on cmp3d.** The own library cuts M 3.8x and law-check visits 1.6x, but raises total visits
  1.46x (37.7M to 55.1M), because building under it costs more (52.0M against 32.8M). On sbo3 both agree (total 10.6M to 6.1M).

Split by region (prototype, reverted: exclusive attribution of counted visits to nested labelled regions, cmp3d, 300 laws, millions
of visits with lemma counts in parentheses):

| region | none | own | own, `NOBDD=1` |
|---|---|---|---|
| case-lemma checks, for the laws' machine proofs | 28.7 (683) | 29.9 (344) | 27.3 (344) |
| `lemma_dd` building (the case lemmas with nv >= 9) | 0 | 11.0 (15) | 0 |
| case-lemma checks inside the mined rules' proofs | 0.3 (104) | 3.8 (188) | 3.8 (188) |
| rewriting and the rest of building | 3.8 | 7.2 | 7.2 |
| law checks | 4.8 | 3.1 | 3.1 |
| total | 37.7 | 55.1 | 41.4 |

- **Checking case lemmas is most of the kernel work** (61-77%). The laws' machine proofs need half as many case lemmas under the own
  library, but each costs about twice as much (87k against 42k visits): the laws the library leaves are the ones with wider machines.
- **By visits the diagram proofs cost more than the case trees they replace, by time they cost less.** All 15 diagram lemmas come
  from the laws' machine proofs (none from the rule proofs). With `NOBDD=1` the same lemmas are case trees: building them costs no
  counted visits (after the `bool0` fix) and checking them costs 2.6M less, so the total falls 55.1M to 41.4M with M unchanged (31).
  But `proof_cost_split` (normal build, own library, pinned to two cores, five alternating runs each, machine load 7-66% from another
  program, so best-of) takes 52.2 s CPU with case trees against 47.1 s with diagrams: building 2^nv-leaf trees costs time the
  visit count does not see. Diagrams stay (`DDMIN=9`). Reversed on 2026-10-13: case trees are now faster at nv = 9 ("Case
  trees at nv = 9"), and at nv = 11 no slower; the diagrams are deleted ("Decision diagrams deleted").
- **Shift visits are cheap.** The `bool0` fix removed 2-3x of the build visits but did not change time (same runs: sbo3 5.7-6.8 s old,
  5.5-6.3 s new; cmp3d 47.5-49.0 s old, 47.1-51.9 s new). So the visit count overweights `shift` and misses term construction; as
  a cost for the miner's objective it needs weights (or construction counts, `take_hc_built`) checked against time first.
- **Even without diagrams the library costs more kernel work than none** (41.4M against 37.7M): its rules' own machine proofs
  (3.8M, checked once) and the longer rewriting outweigh the cheaper law checks.

