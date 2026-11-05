## 39. Four leftovers from §37's review -- found and fixed

- **A debug panic in the proof walkers.** `kernel_verify` on
  `\n. (\g. g 1) (\x. \y. x + y) n` panicked in `debug_assert_has_type`.
  `\g. g 1` gives `g : Clo_1`, but the argument is a `Clo_2`:
  `Denoted::Clo` carries no arity, and the three `denote_*` walkers passed
  any `Clo` argument through. The kernel rejects the composed term, so a
  release build was sound, just noisy in debug. `arg_denotation` now
  compares the argument's `return_type_of` with the parameter's arity at
  all six argument sites. The JIT still compiles the term, from its
  specialisation `\n. 1 + n`. Test:
  `a_closure_argument_of_the_wrong_arity_gets_no_proof`.
- **An overflow in the specialiser.** `occurrences` counted tree
  occurrences through a shared DAG as a `usize`. `t + t` nested 70 times is
  71 nodes and 2^70 occurrences: a debug overflow panic, and in release a
  wrap to 0 that the OnceInLam policy reads as "unused". Only 0, 1 and
  "more" matter, so the count is capped at 2.
- **An independence-scanner bypass.** `use crate as x` (or `extern crate
  self as x`, and the same for `super` and `tatic`) let `x::eval` past the
  allowlist, since no `crate::` follows. The scanner now rejects any of
  those roots followed by `as`. `independence.rs` had no tests of its own;
  it has two now, one of which failed before the fix.
- **`find_spine`'s `!in_fn_pos` guard** (§37) now has a test. Without the
  guard, `(\x. \g. g x + g x) 5 (\y. y + z)` has its inner spine
  `(\x. ..) 5` reduced on its own, although the whole spine is declined
  because the capturing closure bound to `g` is used twice.

Each test was seen to fail with its fix removed.

