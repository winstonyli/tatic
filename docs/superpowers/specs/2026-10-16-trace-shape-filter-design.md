---
status: done
---

# Trace shape filter: skip traces a rule's left side cannot match

Status: implemented on branch `trace-shape` (2026-10-16); results in docs/tier-cycle.md, "Lever 2 done". From docs/tier-cycle.md,
"Survey: the next lever, profile at 9b701ec", lever 2 (its numbering; "lever 1" in the chat that asked for this). As built: the
child class is the existing `class(&Term)` that `RuleTable` filters on (no second classification), and `may_match` is folded into
`any_match`, its only caller.

## Problem

The rule miner asks, many times per round, whether a rule's left side `l` matches any term of a trace (the terms `rule_step`
was asked about while rewriting one law, with which rule fired on each). Each question is a scan of the whole trace with
`matches(l, t)` (`match_pat`). In the 9b701ec profile `match_pat` is 5.1% of a sweep's CPU in its own code:

- 2.7% under `touches` (search.rs:897-902: each candidate against each law's trace, to find the laws it can change) and
  `nowhere` (921-923: which of a candidate's fresh memo entries may join the shared memo);
- 1.4% under the speculative `finish` calls (1130); `finish` runs `state` and `pick_kept` (search.rs:1042-1046), so these are the
  same scans;
- the rest under `rule_step_in` (the rewriter itself, not a trace scan, out of scope).

The same scan shape, with a set of left sides, is in `state` (871: the memo entries the rules that changed cannot touch) and in
the test `filtered_memo_entries_hold_under_an_extra_rule` (rewrite.rs:2687), through `RewriteMemo::filtered`.

Most scans answer "no". A match needs `t`'s root operator to be `l`'s, and each non-variable child of `l` to have the same kind
of root as `t`'s child. A summary of which (operator, child kind) pairs occur anywhere in a trace answers most "no"s without
touching the terms: one AND per trace.

## Design

One signature, computed once per term when it is interned, and one summary per trace, computed when the trace is made.

1. **`Term::shape() -> u64`**, a field of `Interned` computed in `Term::op` beside `size` and `vars`, and constant for leaves.
   A node's class is `V`, `Zero`, `Ones` or `Op(o)` (11 classes; 8 operators). The shape of `Op(o, a, b)` has three bits set:
   `bit(Root, o)`, `bit(Left, o, class(a))`, `bit(Right, o, class(b))`, each a fixed index in 0..64 (176 side pairs fold into
   the bits left after the 8 root bits, so some share a bit). A leaf's shape is one bit for its class.
2. **`Term::needs() -> u64`**, for a pattern: the bits a term must have for `match_pat(self, t)` to succeed. `V`: 0 (matches
   anything). `Zero`, `Ones`: their class bit. `Op(o, a, b)`: `bit(Root, o)`, plus `bit(Left, o, class(a))` unless `a` is a
   variable, the same on the right. Computed on demand (patterns are few and small), or stored too if a profile asks.
3. **`Trace`** in rewrite.rs, replacing `Vec<(Term, Fired)>` in the two places a trace is kept: `Rewritten::trace` (the memo's
   entries) and the third field of the miner's `base_eval` rows (search.rs:807, 854). It holds the items and `shapes`, the OR of
   their terms' shapes, set when it is built (both places build the vector once and never push to it after). Methods:
   - `may_match(&self, l) -> bool`: `self.shapes & l.needs() == l.needs()`;
   - `any_match(&self, l, also: impl Fn(&Fired) -> bool) -> bool`: `may_match` first, then the scan as today;
   - `items(&self) -> &[(Term, Fired)]`, for the memo hit that copies an entry's trace into `RULE_TRACE` (rewrite.rs:2049) and
     for `summarize`. `RULE_TRACE` stays a plain vector: it is the accumulator traces are cut from.
4. **Every trace scan goes through `Trace`**: `touches`, `nowhere`, `state`'s changed-rules filter (a set of left sides: the
   trace is scanned when any of them may match), and the test at rewrite.rs:2687. `score_laws`' rows change type, so
   `summarize` and the two callers at search.rs:1182-1184 follow. `RewriteMemo::filtered` passes `&Trace` to `keep`.

**Soundness.** If `match_pat(l, t)`, then `t`'s root has `l`'s operator, and every non-variable child of `l` has the same class
as the corresponding child of `t` (`match_pat` compares node kinds before recursing). So `t.shape()` has every bit of
`l.needs()`, and so does the OR over a trace containing `t`. A shared bit only weakens the filter. Hence `may_match` is false
only when no term of the trace matches, and every scan answers as before: outputs cannot change.

**Not covered.** `applicable` (search.rs:715-722, candidate generation) scans subterms of the stragglers, not a trace; it is not
in the profile. The same shape could cover it with a subterm summary per term (the OR of the shapes of all subterms, also
bottom-up), but that is a second field for a cold path, so it is left out. `rule_step_in`'s own `match_pat` calls (rule lookup in
the rewriter) are a different question and not touched.

## Falsify first (probe, throwaway)

The ceiling assumes most scans answer "no" and that the filter catches most of those. Before building `Trace`, a probe on main
counts, over one salt-1 sweep, at `touches`, `nowhere` and `state`: the scans, the scans that find a match, and the scans the
mask would reject (computing shapes on the fly). And it counts `match_pat` calls in those scans against the calls left after
the filter. Go on only if the filter removes at least half of the scans' `match_pat` calls; otherwise record the negative
result in docs/tier-cycle.md and stop.

## Testing and measurement

- Unit check (new test in rewrite.rs): for terms from the parse tests and every rule of a small library, `match_pat(l, t)`
  implies `t.shape() & l.needs() == l.needs()`, plus a case where the filter rejects (so the check would catch a mask that
  always passes).
- The existing `filtered_memo_entries_hold_under_an_extra_rule` runs through `Trace` unchanged in meaning.
- Gate: `hc_seq.sh` and `gate_cmp.sh`, identical outputs on salts 1 and 2 expected (a pure filter).
- Timing: `hc_rounds.ps1` against main, with load and RTP reported; expected at most about 4% of job CPU, so a quiet machine is
  needed to see it (the spread between runs is about 1 s of 12-13 s).

## Costs and risks

- A `u64` more per interned node (nodes are never freed; `size` and `vars` are already there).
- `Trace` touches the miner's types and `RewriteMemo::filtered`'s signature: one migration of every caller, no shim.
- If traces are short or most scans match, the filter saves little: that is what the probe is for.
