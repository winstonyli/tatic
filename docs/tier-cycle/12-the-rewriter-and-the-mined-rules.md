## The rewriter and the mined rules

### Derivability prune (negative, 2026-10-10)
Prototype (reverted): drop each rule that the built-in rules plus the earlier kept rules prove machine-free (`rewrite_law`, width 4),
in mining order as Enumo's `minimize`. It dropped 1 of 8 (add3), 0 of 8 (sbo3, cmp3d), 2 of 25 (u3, salt 1) and 3 of 28 (u3, salt 2)
rules. M on 300 held-out shuffled laws (salt 1, skip 1000; CHECK_FAST) rose with the pruned library: u3 salt 1 sbo3 30 -> 49,
cmp3d 9 -> 15; u3 salt 2 sbo3 49 -> 51, cmp3d 13 -> 14; add3 0 -> 0. A derivable rule is not redundant for a directed, budgeted
rewriter: it is a shortcut (Enumo's fast-forwarding makes the same point). The libraries are already almost irredundant, so the
25-rule plateau is not redundancy. Any prune must be judged by M, not derivability.

### A rewrite cycle behind cmp3d's leftover laws (2026-10-10)
Of the 31 cmp3d laws that need a machine proof under the own library, 20 used up the whole rule budget (200 steps; no law does
without a library; sbo3: 2 of 17). The cause is a cycle between a mined rule and the built-in ones:
`lt(x, sub(y, z)) -> lt(x, add(sub(x, y), z))` (mined) undoes `lt(x, add(x, y)) -> lt(x, sub(0, y))` and `sub(x, 0) -> x`
(built in), so `lt(y, add(y, z))` loops until the budget runs out. The budget is shared by both sides of a law, so the other side
is left half-normalised, and the pair needs a machine proof that is larger than the one without the library (more carries, for
example 6/4 instead of 4/4; `normal_forms` now prints them). 9 of the 31 laws need no machine proof at all without the library.
On the same 31 laws the kernel visits are 11.6M without the library and 48.1M with it.

The mined rule grows in the rule order (`x` occurs twice on the right), so the order check would reject it; it got in as a
*cross-side* rule (three or more variables, abstracted from the two sides of a law), which the miner admits without an order
check, leaving the budget as the only guard against cycles (`search.rs`, `ok_order`). Its reverse direction goes down in the order.
**Ordering cross-side rules makes M worse (negative, reverted).** Orienting each cross-side candidate by the rule order (reversed
when only the reverse goes down, dropped when neither does), re-mining the salt-1 libraries and re-running the loops (count-only)
raised total M everywhere: cold 542 to 624 (cmp3d, add3, sbo3), seeded cmp3d 109 to 153, add3 62 to 124, sbo3 41 to 122; the
libraries' own mining streams went from 45 to 80 (cmp3d). The growing cross-side rules do useful work in every family, not only the
one that cycles. Some ordered runs still used up the budget (sbo3 seeded: up to 6 laws in a batch), so the order alone does not
stop it either.

Kept: a tripwire. `rule_set_kernel_check` counts the laws that used up the rule budget (`CHECKED ..., N used up the rule budget`),
and `scripts/loop_stream.sh` writes it as the sixth column of `m.tsv` and as `exhausted=` in its last line. cmp3d's own library: 23
of 300 laws; no library: 0.

### Per-side rule budget; rejecting cycling candidates is a negative result (2026-10-11)
**Each side of a law now gets the whole budget** (`rewrite_law`). Afterwards the budget is what the hungrier side left, so the
tripwire still counts a law whose either side used it up. With libraries re-mined under it (salt 1; sbo3's library is unchanged,
add3's and cmp3d's differ by one rule each), total M against `loop_dd1` (shared budget):

| | cmp3d | add3 | sbo3 |
|---|---|---|---|
| cold | 231 to 224 | 183 to 183 | 128 to 121 |
| seeded (own library) | 109 to 74 | 62 to 67 | 41 to 40 |

On cmp3d's 300-law timing batch, the old library cut M from 31 to 24. Wall time pinned to two cores on a quiet machine
(load 9-14%, RTP off; best of two runs, alternating):

| exe | no library | own library |
|---|---|---|
| shared budget | 47.7 s | 46.1 s |
| per-side budget | 47.3 s | 34.6 s |

So the own library now saves 1.37× instead of 1.03×. sbo3's batch is unchanged at 5.8 s. The cycles themselves remain: 28-32
seeded cmp3d laws per stream still use up the budget, now on one side only.

**Rejecting a candidate that makes a mining-batch law use up the budget makes M worse (negative, reverted).** The miner scores at
40 steps (`RULEMINER_STEPS`). With the old libraries, 197 of sbo3's 200 mining-window laws normalize in at most 40 steps and 3
cycle, so a 40-step budget does detect the cycles. But rejecting every candidate that makes even one law cycle throws out the
best rules. sbo3 lost `add(sub(x, y), z) -> add(sub(z, y), x)` (+18 fixed). The libraries' own windows went from 12 to 24
(sbo3), 20 to 35 (add3) and 45 to 51 (cmp3d), and mining took about twice as long. Loops (with per-side budget too) gave seeded
cmp3d 103, add3 91, sbo3 56 against 74 / 67 / 40 without the rejection, and cold 222 / 195 / 144. No law used up the budget in
any of those runs. A cycle on a few laws costs time; a rejected rule costs M on many.

**Why ordered sbo3 still cycled** (the oriented runs above). It is a true cycle, not 200 steps being too few. On
`sub(sub(z, x), sub(y, z))` five steps repeat until the budget runs out:
`sub(sub(x, y), z) -> sub(x, add(y, z))`, `add(x, sub(y, z)) -> sub(x, sub(z, y))`, and three uses of the permutative
`sub(x, sub(y, z)) -> sub(z, sub(y, x))`. By default, a rule is checked once against the rule order, or for a tie against a rule-level
tie-break (`rule_order_or_tie`), and then fires on every instance unchecked. Only permutative rules are checked per instance, and
then by `show()` order. Those are different orders, so steps that mix them need not terminate. `PERM_ORDER=lpo` checks every tied instance against
one path order. On those three batches it removes all 7 exhausted laws, but M rises from 8 to 18, with libraries mined under the
default order.

Diagnostics kept: `rule_set_kernel_check` prints `EXHAUSTED <law>` per law; `normal_forms` gives each side its own budget and
prints `steps a/b`.

### Cycle cut; lpo and a cycling penalty are negative results (2026-10-11)
Three ways to stop the rewrite cycles, each with libraries re-mined under it (salt 1, per-side budget), total M (cmp3d / add3 / sbo3):

| | cold | own library | laws using up the budget, own |
|---|---|---|---|
| per-side budget (baseline) | 224 / 183 / 121 | 74 / 67 / 40 | 91 / 60 / 11 |
| `PERM_ORDER=lpo`, mined and served | 262 / 223 / 189 | 170 / 154 / 156 | 128 / 0 / 0 |
| miner penalty (`RULEMINER_CYCLE=1`) | 228 / 195 / 135 | 74 / 61 / 40 | 92 / 16 / 11 |
| **cycle cut** | **214 / 183 / 123** | **68 / 61 / 35** | **0 / 0 / 0** |

- **lpo (negative, deleted).** Checking every tied instance against one path order costs too much coverage: the libraries mined
  under it are worse everywhere, and cmp3d's unordered cross-side rules still cycle. `PERM_ORDER` is gone, with the older `tie`
  mode (section 87, never the default and not rerun), since the cut covers the cycles both modes targeted.
- **Penalty (negative, deleted).** A newly cycling law costs the candidate what a lost fix would. It helps own add3 (61 vs 67)
  and loses on every cold stream (+47 in all).
- **Cycle cut (kept, default).** Rewriting is deterministic apart from the step budget, so `rewrite(t)` called while `t` is
  already being rewritten further out can only repeat that work. `rewrite` keeps the path of terms in progress and returns `t`
  unchanged (proof `refl`) on a repeat, so the chain ends after one lap instead of at the budget. The rewrite memo does not cache a
  result that a cut shaped, and replays an entry only where the path in force cuts none of the terms it took up (law 168 under
  Open). Tests: `rewrite_cycles_are_cut` (sbo3's five-step cycle; fails with the cut disabled), `memo_hits_match_fresh_rewrites_under_cycling_rules`.

Serving time with the cut, on the 300-law calibration batches (pinned to two cores, quiet machine at 5-15% load, RTP off; best of two
alternating runs):

| batch | no cut, per-side libraries | cut, same libraries | cut, libraries mined under it |
|---|---|---|---|
| cmp3d | 34.3 s (M 24, 23 exhausted) | 26.2 s (M 21, 0 exhausted) | 26.0 s (M 21) |
| sbo3 | 5.7 s (2 exhausted) | 5.2 s | 5.0 s |

So the cut alone makes cmp3d serving 1.31× faster. Against no library (47.3 s, measured earlier without the cut), cmp3d's own library now saves about 1.8×,
up from 1.37× (per-side budget) and 1.03× (shared budget).

Cross-family transfer was rerun under the per-side budget (`docs/loop-result.md`, findings 3-4; that file was deleted with
the families' results on 2026-10-26: `git show 00a21d9:docs/loop-result.md`).

### Why add3 did better with sbo3's library; scoring every orientation is a mixed result (2026-10-11)
The miner keeps one candidate per left side before scoring: the smallest right side, ties broken by `show()`. For add3's
`sub(sub(x, y), z)` that kept `sub(sub(x, z), y)` (permutative) and dropped `sub(x, add(y, z))`, which sbo3's library has. So add3's
library oriented its `sub` chains the other way. Serving add3 batch 0 (salt 1, phases 1-3) with its own library, sbo3's, and its own
with the two chain rules swapped for `sub(sub(x, y), z) -> sub(x, add(y, z))` gives M 46, 36 and 27.

Scoring every right side per left side (re-mined at salt 1, total M):

| | add3 | sbo3 | mix3 | cmp3d |
|---|---|---|---|---|
| mine, one per left side / every | 18 / 10 | 12 / 12 | 14 / 9 | 30 / 31 (96 s / 427 s) |
| own loop | 61 / 40 | 35 / 41 | | 68 / 91 |
| cold loop | 183 / 173 | 123 / 124 | | 184 / 214 |

It fixes add3 and mix3 but makes sbo3's and cmp3d's own loops worse and cmp3d's mine 4.5x slower (each left side's rivals are scored
separately). Kept one per left side.

Rescoring only the winner's rivals (a rival replaces the winner on a strictly higher gain, proved lazily) costs little. On add3's
mine it took `sub(sub(x, y), z) -> sub(x, add(y, z))`, the rule sbo3 has. Still mixed (salt 1, total M, committed miner / rivals):

| | add3 | sbo3 | mix3 | cmp3d |
|---|---|---|---|---|
| mine | 18 / 5 | 12 / 12 | 14 / 9 | 30 / 43 (96 s / 163 s) |
| own loop | 61 / 28 | 35 / 35 | | 68 / 83 |
| cold loop | 183 / 179 | 123 / 130 | | 184 / 211 |

cmp3d's loss comes from greedy myopia, not from the rival. Its round 3 took the rival `add(sub(x, y), z) -> sub(add(x, z), y)`.
Round 5 then took the inverse `sub(add(x, y), z) -> add(sub(x, z), y)` at -1 fixed laws for a 7697 size cut, and the pair cycles
(cut after one lap). Reverted; the patch is not kept.

Refusing such winners does not rescue it (salt 1, total M; a refused candidate scores gain 0):

| variant | own add3 / sbo3 / cmp3d | cold add3 / sbo3 / cmp3d |
|---|---|---|
| committed miner | 61 / 35 / 68 | 183 / 123 / 184 |
| refuse a winner that uncovers any covered law | 115 / 86 / 82 | 188 / 155 / 203 |
| rivals + that refusal | 89 / 79 / 71 | 173 / 154 / 219 |
| rivals + refuse a net loss in covered laws | 28 / 35 / 94 | 179 / 130 / 211 |

- **The per-law refusal is far worse everywhere.** Good rules that fix many laws often uncover one, and its mines fall behind too
  (ref M: sbo3 12 to 20, add3 18 to 38).
- **The net refusal does block cmp3d's inverse rule.** Its cold loops are identical to rivals alone, but cmp3d still loses (ref
  mine M 46, own loop 94 with 4 laws using up the budget). The rival itself is the problem there. `add(sub(x, y), z) ->
  sub(add(x, z), y)` scores +43 fixed under the miner's 40-step budget, yet serving the same laws under the 200-step budget leaves
  more machine proofs. Mining and serving disagree on it.

All variants reverted. A rival orientation is worth revisiting only once the miner scores rules the way serving uses them (the
same budget), or the gap between the two is understood.

### cmp3d's library lost its general rules to the round cap (2026-10-11)
After the growth cut, cmp3d's ref mine (salt 1, 400 laws, 8 rounds) no longer picks `sub(sub(x, y), z) -> sub(x, add(y, z))` or
`add(sub(x, y), z) -> add(sub(z, y), x)`. Both are still candidates. After the four big rules (+32, +41, +34, +20 fixed) they are
worth little on cmp3d's own laws, and the 8-round cap ends the mine first: rounds 5-8 fix +6, +3, +3, +1. With 16 rounds they
come back in rounds 10 (+1) and 12 (+3). Rounds 13-16 fix nothing and only shrink terms. Seeding loops with that 16-rule library
(salt 1, total M; `driver::loop_stream` with `LOOP_MODE=ref ROUNDS=16`, then `driver::sweep` stages `cross:add3,sbo3 own:cmp3d`):

| seeded loop | 8-round cmp3d library | 16-round |
|---|---|---|
| add3 | 147 | 57 |
| sbo3 | 95 | 59 |
| cmp3d (own) | 68 | 60 |

The loops seeded from add3's and sbo3's libraries reproduced exactly (48, 46). A rule worth +1 on its own family can be worth
dozens of laws on another, so a family's mine can't judge transfer, and a round cap set for one family's laws trims general rules.
`driver::sweep` now runs every ref mine with 16 rounds (loops still mine 8 per batch). Rerun at salt 1 (stages `mines own cross
pooled:mix3`; cold loops don't use a library): add3's and mix3's mines stop by themselves at 8 and 2 rules (libraries unchanged),
sbo3's at 10 (two `or` rules added; own loop 35 to 31), and cmp3d's reaches the cap (mine 83 to 109 s). Every seeded total is
equal or lower; the changed ones are those above and sbo3's own.

**No cap (kept).** Uncapped, cmp3d's ref mine stops by itself at the same 16 rules (it stops once no candidate fixes a law or
shrinks the terms), so every library is identical. The cap still cut 8 of the loops' per-batch mines at 8 rules. Removing it
everywhere (`RULEMINER_ROUNDS` and the driver's `ROUNDS` now default to no cap) left every seeded total equal or lower (sbo3 from
add3's and cmp3d's libraries 48 to 47 and 59 to 58) and cut cmp3d's cold loops from 180 to 167. A stop rule such as "two rounds
without a fixed law" was not needed. The full sweep (`mines own cold cross cold:mix3 pooled:mix3`) took 638 s.

**Scoring on other families' laws (mixed result).** The direct way to score a candidate on laws outside its family is to mine on
their union: `mines:u3` (stride 11, B=100, K=4, uncapped) stopped by itself at 17 rules (70 s), then stage `mixed` seeds the
loops with it. Salt 1, total M, cold / own / pooled / u3: cmp3d 167 / 60 / 60 / 42, add3 183 / 60 / 42 / 57, sbo3 123 / 31 / 32 /
41, mix3 (held out) 60 / - / 10 / 17. The u3 library is the best one for cmp3d but worse than the pooled one elsewhere, mix3
included. It takes add3's `sub` chain orientation (`sub(x, add(y, z)) -> sub(sub(x, y), z)`, `sub(sub(x, y), z) -> sub(sub(x, z),
y)`), the one that conflicts with sbo3's and that the pooled library drops (see "Why add3 did better"). Scoring on more laws does
not fix an orientation choice, so the union mine does not replace pooling. Salt 2 agrees (u3 best only for cmp3d: README table).

**Down-weighted foreign stragglers (negative, reverted).** A prototype `RULEMINER_FOREIGN=<family>:<stride>:<laws>,..` also scored
the stragglers among the other families' phase-0 laws (each ref mine's window; disjoint from the loops' phases 1-3), each fix
worth 250 against 1000 for an own law, with candidates still drawn from the family's own stragglers only. The general `sub` rules
then win the first rounds (on sbo3, +25 to +52 foreign fixes each). But the uncapped miner already picks them, so the libraries
barely change: sbo3's only reorders, add3's adds one rule, cmp3d's mostly reorders (one comparison rule swapped for two others).
Salt 1, total M, baseline / foreign: own add3 60 / 57, cmp3d 60 / 58, sbo3 31 / 31; add3 from cmp3d's library 57 / 64; pooled
add3 42 / 47, sbo3 32 / 37, cmp3d 60 / 58, mix3 10 / 10; other cross cells within 1. Ref mines took 1.6-2x longer (cmp3d 118 to
187 s). Mixed at best and costlier, so reverted. The pooled cells moving with a reorder alone (sbo3's library holds the same
rules) means rule order affects serving, which no experiment here controls.

### Rule order (2026-10-11)
`rule_step` applies the first rule whose left side matches, so overlapping rules give different normal forms in different list
orders. Serving the salt-1 pooled library (no mining, phases 1-3, total M) in its mined order and five shuffles: add3 53 and 47-62,
sbo3 43 and 38-52, cmp3d 63 and 63-70. A spread of up to 15 laws from order alone is as large as many differences in the tables
above (and explains the pooled cells that moved with a reordered library in the foreign-straggler test).

**Fix (kept):** `set_extra_rules` installs the run-time rules most specific first (larger left side first, ties by text), and every
write to the rule table (`RULE_TABLE`) goes through it, so any order of the same rules serves identically (test `rule_order_does_not_change_rewriting`,
which fails without the sort). Ordering by text alone gave the same totals on this library; specificity was kept because a
specific rule is usually an exception to a general one. Served in all six orders: cmp3d 63, add3 47, sbo3 45 every time. The miner
scores candidates in the same order, so mining and serving still agree, and its memo argument holds (a rule that matches no traced
term changes nothing wherever it sits).

Re-baselined with the full sweep (`mines mines:u3 own cold cross pooled mixed cold:mix3 pooled:mix3 mixed:mix3`, salts 1 and 2;
README table). Ref mines reach far lower M with more rules (salt 1: sbo3 1 with 18 rules, was 10 with 10; add3 8 with 16, was 18
with 8; cmp3d 13 with 31, was 24 with 16; u3 5 with 35, was 16 with 17), and the loops seeded with a family's own or the pooled
library roughly halve (salt 1 / 2: add3 own 30 / 33, was 60 / 46; cmp3d own 33 / 40, was 60 / 61; sbo3 own 27 / 40, was 31 / 48;
pooled add3 27 / 33, sbo3 24 / 38, cmp3d 36 / 43, mix3 7 / 17). One regression: cmp3d's 31-rule library seeds other families
much worse (add3 108 / 100, was 57 / 87; sbo3 91 / 105, was 58 / 82), though still far below cold. cmp3d's ref mine takes 206 s
(was 118 s).

**The regression is one lost general rule.** cmp3d's new library gained 22 specific `lt` rules and lost 7, among them `add(sub(x, y),
z) -> add(sub(z, y), x)`. Appending that one rule (salt 1 loops) takes add3 from 108 to 65 and sbo3 from 91 to 58, leaves cmp3d's
own loop at 33, and leaves the control cells (add3 from sbo3's library 38, sbo3 from add3's 51) unchanged. As with the round cap,
a rule worth little on its own family (here the specific `lt` rules already cover those laws) is dropped, though it is what
transfers. The pooled library carries add3's and sbo3's general rules, so it is unaffected.

**Specific first is not an arbitrary choice.** Serving the salt-1 pooled library (no mining, phases 1-3) under three orders, total
M cmp3d / add3 / sbo3: specific first 43 / 34 / 29 (sum 106), general first (smallest left side first) 68 / 53 / 48 (169), mined
list order 68 / 50 / 45 (163). That library was mined under specific-first, which favors it, but the older pooled library mined in
list order also served better under it (155 vs 159). Order matters this much, so options for later (parked): learn a priority
per rule in the miner (fits the order to the batch, and pooling reopens it), learn which rule wins at each overlapping pair
(needs a critical-pair finder), or complete overlapping pairs Knuth-Bendix style so the order stops mattering (most work; the
step budget and cycle cuts would bound it).

**How many pairs overlap.** `rewrite::rule_overlaps` (syntactic unification, variables renamed apart) lists every pair whose
left sides unify, the second at a non-variable position of the first; `OVERLAP_RULES=<file>` with the ignored test
`rule_overlap_report` prints them. In the salt-1 pooled library (56 rules) all 56 rules overlap something: 1035 ordered pairs,
of which 817 are below the root (the inner rule rewrites a subterm the outer one would match; rule order does not decide these,
the traversal does), 100 are at the root with one left side an instance of the other (specific first settles these), and 118 at
the root otherwise (59 unordered pairs; there specific first is only a size-then-text tie-break). Most of the 118 are comparison
rules (`lt(x, sub(y, z))` against a dozen `lt(.., sub(y, add(..)))` rules); the rest are the `sub`/`add` chain orientations, e.g.
`sub(x, sub(y, z)) -> add(sub(x, y), z)` against `sub(sub(x, y), z) -> sub(x, add(y, z))`. So learning a winner per overlapping
pair means about 60 decisions at the root, and completion would face about 1000 critical pairs: per-pair learning is a modest job,
completion a large one.

**Keeping general rules by a tie-break: no-op.** The miner's candidates are already sorted by left side size (one per left side,
`search.rs`), and a round's winner breaks gain ties toward the earlier candidate, so ties already go to the smaller left side.
The lost cmp3d rule was not tied: under specific first, the specific `lt` rules already cover its laws, so it gains nothing on
cmp3d. Keeping it needs a gain from laws outside the family (the union mine and foreign scoring above), or a library made by
pooling.

**Children first is right (outermost is a negative result).** `rewrite` normalizes a node's children before trying rules at the
node, so an inner overlap goes to the inner rule. A switch that tried the library rules on a node before its children (removed)
served the salt-1 pooled library at cmp3d / add3 / sbo3 205 / 71 / 34, against 43 / 34 / 29.

**Conflicts that happen.** `RULE_CONFLICTS=1` makes serving (`search::rule_set_kernel_check`) count, per term rewritten, each later
rule that would also have rewritten it, and print `CONFLICT <terms> <winner>  OVER  <loser>` (`WITH` since preferences
went, 2026-10-23). Serving the salt-1 pooled library
hits 63 distinct pairs on phase 0 and 62 on phases 1-3, some with built-in and promoted rules (the static count covers only the
library's own rules).
The most frequent (252 terms on phases 1-3) is between two pooled rules with the same left side, `sub(x, sub(y, z))` rewritten to
`add(sub(x, y), z)` or to `add(sub(z, y), x)`: pooling concatenates libraries, so it can keep two orientations of one left side,
and then only the text tie-break picks. The switch was removed with nothing setting it (cleanup CU4e, 2026-10-27); read it with
`git show b984ec2:tests/church_bv/rewrite.rs` (`print_rule_conflicts`, `rule_step`).

**Learned preferences.** Lines `winner  OVER  loser` in a library (`rules.txt`; first a `RULE_PREFER=<file>` switch): where both
rules would rewrite a term, the winner does, whatever the order. `scripts/prefer_flips.sh` learns them for a library: it collects the
conflicts on phase 0, serves each flipped pair alone on phases 0-3, and keeps the flips that lower phase 0's M (about 20 min with 3
workers). Total M over cmp3d, add3 and sbo3, train (phase 0) and test (phases 1-3):

| pooled library | conflicts | kept | train | test |
|---|---|---|---|---|
| salt 1 | 63 | 4 | 26 to 20 | 106 to 89 (cmp3d 43 to 40, add3 34 to 26, sbo3 29 to 23) |
| salt 2 | 42 | 3 | 28 to 27 | 142 to 137 |

Phase 0 predicts the rest: at salt 1, every flip that lowered phase 0 lowered phases 1-3, and the worst flips on phase 0 were the
worst on phases 1-3. The salt-1 winners let a `sub(x, sub(y, z))` rule beat `sub(sub(x, y), z) -> sub(x, add(y, z))` (-13 test
alone): the specific-first order is wrong there. Preferences are per library: the salt-1 file on the salt-2 library gives 142 to
136. At salt 2, three flips each give -4 train and -11 or -8 test alone, but kept together only -1 and -5: two of them demote the same
rule in favor of different winners. Keeping flips one at a time and rescoring the rest after each (greedy, like the miner's rounds)
should recover that. The serving runs use no mining (`LOOP_MODE=none`), so these are serving gains on a fixed library. Learning them
inside the miner is measured below: a family's own mine hardly ever has conflicts to learn from.

### Ablating the fixed rewriter and prover parts (2026-10-11)
`ABLATE=<names>` switches off one hand-written part. Serving only (`LOOP_MODE=none`, `CHECK_FAST=1`) on phases 1-3, salt 1, total
M over cmp3d, add3 and sbo3, with the salt-1 pooled library and with no library:

| ablated | pooled library | no library |
|---|---|---|
| nothing | 106 | 828 |
| `zero`, `not`, `chain`, `fold`; in `prove_eq`: `eq_pos`, `eq_cong`, `eq_bitcong`, `shrmask`, `generalize` | 106 | 828 |
| `eq_truth` (truth table over atoms) | 110 | 832 |
| `collapse` | 185 | |
| `promoted` (the 35 promoted rules) | 234 | |
| the 21 built-in `rules()` | 257 | |
| `tree` | 318 | |
| `assoc` | 373 | |
| `comm` | 880 | |

Nine parts never decide a law on these streams, with or without mined rules; all names are wired (`eq_truth` and the others move
M). With no library they also change nothing on mix3, cmp3, u3 and u3w (111, 5, 299, 327). But the unit tests need two of them for
`shr1` laws, which these streams never send through them: without `eq_pos` the built-in `shrnot` rule's laws need a machine
proof (`shrnot_rule_is_provable_and_closes_the_shr_not_laws`), and without `shrmask` that test and
`shr_mask_proves_root_shift_laws_over_arithmetic_and_rejects_false_ones` fail. The other seven (`zero`, `not`, `chain`, `fold`,
`eq_cong`, `eq_bitcong`, `generalize`) can each be off with every unit test passing. The two-variable families (shl, shr, lt,
mul) were not served.

**Deleted (2026-10-11): six of them.** Switching all seven off at once raised M (pooled 106 to 123, no library 828 to 870):
`zero` (`x + 0`) and `chain` (sums a constant carry reduces, `x + 0` among them) cover each other, so each alone looked
redundant. With either one back, all seven families and both libraries give the numbers above exactly. `chain` stayed, as the
general case; `zero`, `not`, `fold`, both congruences and `generalize` (with `shared_subterm` and `GENERALIZE_ABOVE`) are
gone. The tests of folding and of large shared sums still pass, now by the remaining steps. One-at-a-time ablation misses
parts that back each other up; check a deletion set together before deleting. `comm` (sorting operands) matters most: the mined rules are learned on top of a canonical operand order. The library was mined
with every part present, so a large rise means the library relies on that part, not that it could not be learned.

### Preferences and rival orientations in the miner (2026-10-11)
Two greedy extensions of the miner, A/B'd with `driver::sweep` (`mines own cold pooled`) at salts 1 and 2:
- **Preferences** (`RULEMINER_PREFS=1`; on during the A/B, now off by default and used only on pooled libraries, below): after
  the rounds, collect the conflicts on the scored laws and flip the pair with the largest gain, rescoring after each flip, until
  no flip gains; the flips are written into `rules.txt` as `winner  OVER  loser` lines, which serving and later mines read.
- **Rivals** (a switch during the A/B, now always on): after a round's winner is chosen, score the other right sides of its left
  side on the same laws; one with a larger gain replaces it, if proved.

Total M (own, cold and pooled loops on phases 1-3; mines is the four ref mines on phase 0):

| | mines s1 | own s1 | cold s1 | pooled s1 | mines s2 | own s2 | cold s2 | pooled s2 |
|---|---|---|---|---|---|---|---|---|
| baseline | 29 | 90 | 447 | 87 | 24 | 113 | 451 | 114 |
| preferences | 29 | 88 | 446 | 87 | 23 | 112 | 450 | 112 |
| rivals | 23 | 74 | 472 | 75 | 21 | 104 | 450 | 158 |
| both | 23 | 72 | 472 | 75 | 21 | 103 | 452 | 151 |

Preferences barely help. The ref mines learned one preference in all, since a family's own rules are chosen one at a time on
top of each other and rarely conflict. The loops' mines learned 13, 8 of them in pooled loops, where conflicts come from
pooling, but the pooled loops' M hardly moved: a batch's mine already adds rules for the laws a conflict breaks, while
`prefer_flips.sh` measured serving a fixed library (106 to 89). The phase also roughly doubled mine times (wall times are rough:
an orphaned sweep shared the machine for the first ~20 min).
Rivals replace 3-4 winners per add3 mine and one per sbo3 mine, all `sub`/`add` chain orientations: add3's own loops drop from
30 to 14 (salt 1) and 33 to 22 (salt 2), and salt 1's pooled loops from 87 to 75. But salt 2's pooled add3 rises from 33 to 71,
and salt 1's cold cmp3d from 163 to 181. Pooling drops two hand-picked add3 orientations that conflict with sbo3's
(`driver::sweep`); the rivals change add3's orientations, so the drop list no longer matches them.

**Preferences learned on the pooled library (kept).** The pooled stage now keeps every library's rules (no hand-picked drop
list) and has each family learn preferences on it: a mine on the family's phase-0 stream (its ref mine's settings) with no rule
rounds, only the preference phase, on the pooled library; that family's pooled loops start from the result
(`pooled_<family>/rules.txt`). It takes 12-68 s per family and learns 0-5 preferences. Pooled loops, total M on phases 1-3,
from the libraries mined with rivals:

| pooled library | salt 1 | salt 2 |
|---|---|---|
| baseline (no rivals, drop list) | 87 | 114 (add3 33) |
| rivals, drop list | 75 | 158 (add3 71) |
| rivals, everything pooled | 67 | 165 (add3 79) |
| rivals, everything pooled, learned preferences | **60** | 129 (add3 43) |

The learned preferences win back most of salt 2's loss, but salt 2's add3 stays 10 above the baseline. The top preference at
salt 2 (+7000 on add3's phase 0) lets add3's own `sub(xor(x, -1), y) -> sub(-1, add(x, y))` beat `sub(x, sub(y, z)) ->
add(sub(x, y), z)` (in all three libraries) on terms both match, against the specific-first order.
Over own, cold and pooled loops and both salts, the kept setup (rivals; preferences only on pooled libraries) totals 1289 against
the baseline's 1302: own and pooled gain, and salt 1's cold loops lose 25 (447 to 472).

**The cold loss is a greedy path loss, not the orientation.** Most of it is cmp3d phase 3 (56 to 69), whose second batch goes
from 6 to 20 after the first batch's mine; every new straggler is an `lt` law. Serving that batch under the first mine's rules:
the base set gives 6, and with only the rival orientation swapped in still 6; the rivals run's set gives 20, and with its winner
swapped back 22. What differs is the rest of the set. The base mine chose the general `lt(x, sub(y, z)) -> lt(x, add(sub(x, y),
z))` (+11 in-sample; without it the base set gives 24). In the rivals run the rival's larger round gain (+14 against +10) won
round 2, the general rule never led a later round, and specific `lt` rules took the rest. Adding the general
rule to the rivals set gives 17, not 6, since the specific rules fire first. The rivals set is worse on the mined batch too, not
only on the next one: its mine covers 38 of the 43 stragglers against the base mine's 42, and serving the mined batch gives M 5
against 1 (14 with the general rule added). So the larger one-round gain led to a worse finished set: greedy myopia, not
overfitting. Salt 2's cold loops do not lose (451 to 450). Lookahead (below) fixes it.

*Held-out scoring (negative, reverted).* Rank each round's candidates by the smaller of their gains on the even- and odd-indexed
stragglers (guard laws in both), then by the full gain. On this loop it changes nothing (69 both ways): most gains are +1, so the
smaller half is 0 for nearly every candidate and the ranking falls back to the full gain; it only swapped the order of the first
two `sub` rules. It targets overfitting, which this loss is not.

**Lookahead on rival swaps (kept; removed 2026-10-26 with the three-variable pool, "Kept: the pool over three variables").** When a rival would replace a round's winner, the mine finishes the rest of its rounds both
ways (greedily, rivals taken, no further lookahead) and keeps the choice whose finished set has the larger value (the gain's
measure as a total; ties to the rival). On the loop above it keeps the winner and reproduces the base run (56; 42 of 43 covered).
Sweeps (`mines own cold pooled`), total M:

| | mines s1 | own s1 | cold s1 | pooled s1 | mines s2 | own s2 | cold s2 | pooled s2 |
|---|---|---|---|---|---|---|---|---|
| rivals | 23 | 74 | 472 | 60 | 21 | 102 | 450 | 129 |
| rivals + lookahead | 23 | 74 | **451** | 60 | 21 | 102 | 450 | 129 |

It overrode 6 of 33 swaps, all in cold loops' mines (cmp3d, add3, sbo3); the ref mines' swaps all held, so own and pooled are
unchanged. All loops now total 1266, against 1302 without rivals. Cost: ref mines 1.8-3.5x slower where swaps occur (add3 42 to
102 s and 49 to 173 s), sweeps 27-29% longer (883 to 1120 s, 988 to 1272 s; two sweeps at a time).

*Lookahead over runners-up too (negative, removed).* Each round's alternatives also took the next best proved candidate (k = 2:
winner's rival, winner, runner-up), each finished greedily. On the cmp3d loop above it changed nothing (56); the sweeps lost
everywhere but salt 2's cold loops: own 74 to 84 and 102 to 117, cold 451 to 467 and 450 to 450, pooled 60 to 65 and 129 to 165
(all loops 1266 to 1348); the ref mines' own M 23 to 21 and 21 to 23, 2-3x slower. A guess, untested: at a rival swap both
sides are the same left side, scored on the same laws, while a runner-up is a different rule, and picking among different rules by
their finished in-sample value fits the mined batch more closely than the greedy choice does.

*Runners-up chosen held out (negative, reverted, 2026-10-12).* A test of that guess: the same three alternatives (rival,
winner, runner-up), each finished greedily on the even-indexed stragglers and valued on the odd-indexed ones, and the other way
round, summed (2-fold; guard laws in both folds; the rounds still choose on every straggler; ties to the earlier alternative).
Sweeps against HEAD (with the rival-scoring fix, same rows):

| | mines | own | cold | pooled | loops |
|---|---|---|---|---|---|
| HEAD | 23 / 21 | 74 / 102 | 451 / 450 | 58 / 99 | 583 / 651 |
| held-out runners-up | 21 / 20 | 85 / 103 | 435 / 454 | 66 / 91 | 586 / 648 |

All loops 1234 both ways: the in-sample version's loss is gone (so the guess holds in part, the in-sample choice overfit), but
nothing is gained. It moves M between families rather than lowering it: cmp3d own 33 to 46 and pooled 31 to 41 on salt 1;
add3 cold 166 to 150 (salt 1), sbo3 pooled 40 to 32 (salt 2). cmp3d's ref mines were 3.5-4.5x slower (266 to 923 s, 170 to
763 s) and the sweeps about 2.3x longer (shared machine). Patch kept out of the repo; the greedy choice stays.

*Lookahead cache (kept, exact; removed with the lookahead 2026-10-26).* A round depends only on the set of rules chosen so far (`set_extra_rules` sorts them), and the
alternatives' greedy paths often reach the same set in another order, so the miner keeps each set's pick and finished value; the
kept alternative's path is also the next rounds' own. Same choices on the cmp3d loop; picks 47 to 36, and 467 to 180 with three
alternatives a round (316 to 137 s). Full sweeps reproduce every own, cold and pooled
row; sweeps 1120 to 747 s and 1272 to 732 s (two at a time), ref mines 472 to 293 s and 435 to 233 s, so the rival lookahead now
costs less than it added.

*Rule-set evaluations reuse the last one's memo (kept, exact).* Each evaluation of a chosen set (`state`) is seeded with the
previous evaluation's rewrite memo, minus the entries whose trace has a term matched by a rule added or removed since
(`RewriteMemo::filtered`). On the cmp3d cold loop, same choices and M 56; time in these evaluations 9.4 to 2.1 s and 1.1 to 0.3 s
per mine, loop wall time best 46 to 38 s (two runs each, alternated, the machine at ~50% load from other work). Full sweeps
reproduce every own, cold and pooled row at both salts (times not comparable: CPU at start 27% against 14%). Keeping the
candidate scorers' memos across picks too would need worker threads that live for the whole mine (the memos hold thread-interned
expressions); not done, since scoring already reuses 87% of law evaluations across rounds (89868 of 103100 on cmp3d).
Not exact for joins until 2026-10-22: a kept failed join stayed failed after the join store gained a path for its pair,
which made a mine loop forever (60d8116; "Hidden twins beyond two-leaf nodes", "A miner hang").

### Operand order: `show()` wins, also with the promoted rules re-learned under each order; comm is not mined back (2026-10-12)
Learning operand order (learned-vs-fixed.md, candidate 1) is only worth it if the order matters and the current one is not
already good. A temporary switch put one term order behind the three places that use it (the bitwise operand sort with constants
last, `add` comm and left-comm, and the instance check of permutative rules) and ran full sweeps (mines, own, cold, pooled) with
the `show()` order, its reverse, and size first (then `show()`), plus `ABLATE=comm` under the `show()` order. A default-order run
reproduced salt 1's HEAD rows exactly. Total M (salt 1 / salt 2):

| | mines | own | cold | pooled |
|---|---|---|---|---|
| `show()` (current) | 23 / 21 | 74 / 102 | 451 / 450 | 58 / 99 |
| reversed | 29 / 29 | 132 / 147 | 500 / 486 | 106 / 89 |
| size first | 20 / 17 | 98 / 117 | 478 / 457 | 76 / 117 |
| `ABLATE=comm` | 86 / 79 | 177 / 222 | 799 / 798 | 161 / 248 |

The order matters (own loops up to 1.8x), and the current one wins 13 of the 16 pairwise comparisons (each stage and salt against each other order); the exceptions are size first's mines and
reversed salt 2 pooled. Per family the picture is a little more mixed (size first: salt 1 pooled sbo3 11 against 14, salt 2 own
sbo3 39 against 40), but no other order wins a family on both salts. Without the built-in comm the miner does not mine it back
usefully (cold loops 451 to 799, 450 to 798), though each library holds one or more `add` swap rules. The 35 promoted rules were
mined under the `show()` order, which biases the test toward it. Without them (`ABLATE=promoted`, same three orders, the probe's
build), the ranking turns over:

| `ABLATE=promoted` | mines | own | cold | pooled |
|---|---|---|---|---|
| `show()` | 33 / 29 | 139 / 164 | 542 / 497 | 125 / 160 |
| reversed | 31 / 34 | 160 / 142 | 524 / 515 | 143 / 124 |
| size first | **19 / 19** | **120 / 118** | **498** / 510 | **88 / 101** |

Size first wins 7 of 8 cells (all but salt 2's cold loops), and `show()` is last or second in every other. Per family the best
order varies: own loops, add3 26 / 28 best under `show()` / reversed (salt 1 / 2), sbo3 31 / 34 under size first, cmp3d 43 /
46 under `show()` / reversed. This suggested the earlier verdict came from the promoted rules, which are worth far more than the order (the
`show()` order with them, own 74 / 102, beats every order without them).

The fair comparison re-promotes under each order by one procedure (below) and sweeps with that set in place of PROMOTED:

| re-promoted under its own order | mines | own | cold | pooled |
|---|---|---|---|---|
| `show()` | 23 / 21 | 74 / 102 | 451 / 450 | 58 / 99 |
| size first | 30 / **15** | 106 / 129 | 475 / 454 | 79 / 124 |

`show()` reproduces HEAD's rows exactly, though its set differs from PROMOTED in 4 rules (below). Size first wins 1 of 8 cells
(salt 2's mines). By family the loss is cmp3d (own 33 / 40 under `show()`, 55 / 68 under size first) and add3 (14 / 22 against 22
/ 36); sbo3 does better under size first on salt 2 (own 40 to 25, pooled 40 to 24) and salt 1's pooled loops (14 to 10). So the
`ABLATE=promoted` reversal came from the missing rules, not from the order: with the promoted rules re-learned under each order,
`show()` wins. Learning one global order is parked (no better order found); the only remaining signal is per family (sbo3 under
size first), which would need the order learned per family together with that family's promoted rules. The switch is removed.

Where PROMOTED came from (design spec part 2, section 60): `rule_miner` on the older mul, shl, lt and shr families (none a sweep
family), on 2026-10-02's miner (before rivals, lookahead, preferences and the growth cut); 20 rules of the first round, then 15
of shr's second-round 17 ("useful", a filter not written down). Their left sides are literal patterns over normal forms in the
`show()` order, so under another order many cannot match. The fair test above re-promotes under each order by one procedure,
with no promoted rules in force: round 1 mines mul (`MULMINER_MAX=5`), shl (300 laws) and lt (150 laws); round 2 mines those and
shr (`RULEMINER_DEEP=1 MINER_SUB=1 RULEMINER_STRIDE=3`, 900 laws) with round 1's rules in force; every chosen rule is promoted.
Each order gives 35 distinct rules. Under `show()` the set is PROMOTED but for 4 rules: it lacks `xor(shl1(-1, 0),
shl1(shl1(-1, 0), 0)) -> shl1(sub(0, -1), 0)` and `sub(-1, sub(x, -1)) -> sub(shl1(-1, 0), x)`, adds `sub(x, xor(x, -1)) ->
sub(shl1(x, 0), -1)` and `shr1(sub(0, -1), 0) -> shr1(0, 0)`, and orients `sub(x, add(y, x))` to `add(0, sub(0, y))`; so the
undocumented "useful" filter changed about two rules. Under size first the set is the same but for 3 rules mirrored in operand
order. Each mine takes 20-100 s.

### Drops of the mine's own rules (negative, removed, 2026-10-12)
Learned-vs-fixed candidate 2 (the miner's greedy search): a chosen rule that later rules make redundant, or that shadows a later
rule, stays, since the preference phase drops only a pooled base's units. A temporary switch made each rule the mine chose a drop
unit of its own (same move, same 2000 floor) and logged every candidate's gain; full sweeps with preferences on in every mine,
with and without it. The two are identical on every stage (salt 1: mines 23, own 72, cold 450, pooled 56; salt 2: 21, 102, 452,
98). Of 642 own-rule drop candidates over both salts, none gains: 6 are 0 and 636 lose. So greedy mines leave no rule whose
removal helps in-sample, even below the floor, and backward elimination has nothing to work on; the greedy loss documented
above ("The cold loss is a greedy path loss") is a path the greedy never took, not a rule it should not have kept. Preferences in
every mine against HEAD: own 74 to 72 (salt 1), cold 451/450 to 450/452, pooled 58/99 to 56/98; mine times not comparable (the
runs shared the machine with other sweeps).

### Rivals scored by counting only (fix, 2026-10-12)
With the promoted rules out (`ABLATE=promoted`), `rule_miner` on shl panicked ("rule mined is not provable") on the rival
`sub(x, shl1(x, 0)) -> sub(shr1(0, 0), x)`: rivals are scored before they are proved, and scoring built each firing rule's proof,
which `add_tree_law` cannot do with `shr1`. Rivals are now scored with `SCORE_ONLY` (counting only; the rewritten terms do not
depend on the proofs), and `score_laws` keeps a caller's `SCORE_ONLY` instead of resetting it. Full sweeps reproduce HEAD's mines,
own, cold and pooled rows on both salts (23/74/451/58, 21/102/450/99).

### Promotion as an iterated sweep: one iteration pays a little, the second does not (2026-10-12)
Aim: move the promoted rules from "learned once" to "learned in the run" (learned-vs-fixed.md). Three framings:
- *Re-run the section-60 procedure inside the sweep* (rejected as a first step): bookkeeping only. Under `show()` it reproduces
  HEAD's rows exactly ("Operand order"), so it moves no number; worth doing only once the iteration below pays.
- *Promote from the sweep families' union* (rejected): already measured as the union mine (`mines:u3`) and as down-weighted
  foreign stragglers, both mixed, with pooling better ("Scoring on other families' laws", "Down-weighted foreign stragglers").
- *Iterate the sweep* (run): a sweep's output is the next sweep's starting base, the cycle's "proved laws compiled into rules
  that make later work cheaper". Today every ref mine starts from the built-in and promoted rules alone. In iteration k+1 the ref
  mine of family F starts from iteration k's pooled library for F (`pooled_<F>/rules.txt`: the three libraries with F's learned
  preferences and drops) and mines its phase-0 stream on top of it.

**Mechanism (kept):** `MINES_WARM=<sweep dir>` seeds each ref mine with `<dir>/pooled_<fam>/rules.txt` through `LoopCfg.warm`,
as the pooled loops are seeded; a family with no pooled library (mix3) mines cold. Iteration 0 is a HEAD sweep (`mines pooled`);
iteration k+1 runs `mines own` with `MINES_WARM` on iteration k, then the existing pooled stage on its libraries. Iteration 1's own
loops against iteration 0's pooled loops isolate what the ref mine adds on phase 0: both serve phases 1-3 from F's pooled base and
mine each batch on top. No leakage: every base is mined on phase 0, the loops serve phases 1-3. Total M (salt 1 / salt 2):

| | ref mines | own | pooled | pooled text lines (with repeats) |
|---|---|---|---|---|
| iteration 0 (= HEAD) | 23 / 21 | 74 / 102 | 58 / 99 | 60 / 47 |
| iteration 1 | 16 / 15 | **55** / 90 | 57 / **85** | 176 / 105 |
| iteration 2 | 14 / 15 | 58 / 85 | 65 / 85 | 529 / 267 |

(Ref mines' M is in-sample, on the phase 0 the base was fitted to.) The falsifier passes: iteration 1's own loops are lower on
both salts (58 to 55, 99 to 90). Best loops: 157 (iteration 0 pooled) to 142 (iteration 1 pooled; 145 own). By family, salt 1
own: cmp3d 31 to 24, add3 13 to 10, sbo3 14 to 21; salt 2 every family at or below. Iteration 2 adds nothing: own 58 / 85, and
its pooled loops lose on salt 1 (65; add3 10 to 16) while the libraries keep growing (salt 1 cmp3d 31, 48, 61 rules). The pooled
text repeats each base once per library (60 to 529 lines), the duplication the per-family pooled text was meant to remove; it
starts to cost at iteration 2 (pooled 65 against own 58, pooled stage 284 to 922 s), but since own loops also stop improving
there, removing it would at best reach iteration 1's rows, so it was not built. The pooled preference mines' phase-0 M (cmp3d
13 / 11 at iteration 0, 7 / 9 after) shows where the room was: cmp3d. Cost of an iteration: about 220-240 s of ref mines and own
loops, plus 260-280 s of pooled stage, two sweeps at a time.

**From `ABLATE=promoted`: the iterations do not recover PROMOTED (negative, 2026-10-12).** The same procedure (`mines own
pooled` per iteration, `MINES_WARM` on the previous one) with the promoted rules out, iterations 0-3, both salts in parallel
(`docs/runs/2026-10-12/scripts/iterate_np.sh`, rows `npit<k>_<salt>`). Total M (salt 1 / salt 2):

| | ref mines | own | pooled | pooled cmp3d text lines | sweep s |
|---|---|---|---|---|---|
| iteration 0 (no promoted) | 33 / 29 | 139 / 164 | 125 / 160 | 60 / 48 | 640 / 916 |
| iteration 1 | 24 / 18 | 115 / 144 | 120 / 140 | 181 / 138 | 389 / 466 |
| iteration 2 | 24 / 18 | 119 / 140 | 108 / 140 | 495 / 387 | 850 / 923 |
| iteration 3 | 23 / 18 | 107 / 140 | 107 / 140 | 1393 / 1102 | 5040 / 2808 |
| HEAD (promoted, iteration 0) | 23 / 21 | 74 / 102 | 58 / 99 | 60 / 47 | |

Salt 2 stops at 140 from iteration 2; salt 1 creeps down (125 to 107) while the sweep slows 8x, the text roughly tripling each
iteration (each warm base is repeated in every library the next pooling concatenates). By family, iteration 3's pooled loops
against HEAD's: salt 1 sbo3 58 against 14, cmp3d 37 against 31, add3 12 against 13; salt 2 add3 47 against 22, cmp3d 54 against
37, sbo3 39 against 40. So PROMOTED stays "learned once": it was mined on the older mul, shl, lt and shr families (above, "Where
PROMOTED came from"), whose patterns these sweep families' phase-0 streams do not supply, and the iterated sweep (which helps on
top of PROMOTED, 157 to 142) is not a substitute for it.

Not run: pooled loops on the held-out mix3 across iterations (`pooled:mix3`). Not tested by any of this: the promoted rules' precedence (they are tried before
the run-time rules, which a warm base is).

