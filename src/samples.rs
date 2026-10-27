//! Sample terms, written as source (`syntax`): the benchmarks' terms, the
//! demo's, and the corpus that unit tests and `tests/golden_wat.rs` run
//! over. One copy, so a bench, a test and the demo that name the same term
//! build the same hash. After `corpus()`, the shapes that unit tests in
//! several files share, outside the corpus.

use crate::syntax;
use crate::term::{Hash, TermStore};

/// Parses `src`, a closed term, into `s`. Panics naming `src` if it doesn't parse: a sample or a test's term that
/// doesn't parse is a bug in that term.
pub fn source(s: &mut TermStore, src: &str) -> Hash {
    syntax::parse(s, src).unwrap_or_else(|e| panic!("sample `{src}` should parse: {e}"))
}

/// Not tail-recursive (the self-call sits under `*`).
pub fn factorial(s: &mut TermStore) -> Hash {
    source(s, "rec f n = if n <= 1 then 1 else n * f (n - 1)")
}

/// A term with the identity and strength-reduction patterns the
/// lemma-database rules target (`x + 0`, `x * 2^k`), so a rewrite has
/// something to win on (bit-vector design doc, section 14).
pub fn redundant_arithmetic_recursion(s: &mut TermStore) -> Hash {
    source(s, "rec f n = if n <= 0 then 0 else n * 8 + 0 + f (n - 1)")
}

/// Naive, exponential; not tail-recursive, so `compile.rs` emits a plain
/// `call`, not a loop.
pub fn fib(s: &mut TermStore) -> Hash {
    source(s, "rec f n = if n < 2 then n else f (n - 1) + f (n - 2)")
}

/// Tail-recursive, 2-ary: `compile.rs` turns the self-call into a
/// `loop`/`br`.
pub fn gcd(s: &mut TermStore) -> Hash {
    source(s, "rec f a b = if b == 0 then a else f b (a % b)")
}

/// Deeper than `gcd`: two base leaves and one tail leaf reached via a
/// depth-2 path, exercising `prove_tail_recursive_universal`'s per-leaf
/// `Ev` construction instead of the single-base/single-tail special case.
pub fn gcd_with_two_base_cases(s: &mut TermStore) -> Hash {
    source(s, "rec f a b = if a == 0 then b else if b == 0 then a else f b (a % b)")
}

/// Tail-recursive, but each iteration creates *and immediately calls* a
/// fresh capturing closure (`\y. acc + y`, capturing `acc`, which changes
/// every iteration) as a literal callee -- a direct-call site (a plain
/// `call`, no `call_indirect`). The closure is only ever called directly,
/// so it is lambda lifted (`lower_wat::direct_only`): `acc` is passed as a
/// parameter and nothing allocates. Until that change it paid one
/// bump-allocator call per iteration, and this bench is where the
/// difference shows (`RELATED_WORK.md` §36). The literal application
/// `(\y. acc+y) n` is also a redex whose argument (`n`, a `Var`) is a
/// value, so `compile_specialised` βv-reduces it to `acc+n` in one step
/// before the term ever reaches the IR builder (`RELATED_WORK.md` §37);
/// this bench measures both changes together, through the JIT.
pub fn capturing_closure_loop(s: &mut TermStore) -> Hash {
    source(s, r"rec f n acc = if n <= 0 then acc else f (n - 1) ((\y. acc + y) n)")
}

/// `add = \x y. x + y`, `caller = \g z. g z`: tail-recursive, and each
/// iteration partially applies `add` to `acc` (one argument short), then
/// completes that partial application through `caller`. The wrapper
/// combinator `register_partial_app` synthesizes for `(add, 1)` compiles
/// once and is shared across every iteration -- only its environment
/// (holding `add`'s own, empty, environment plus the current `acc`) gets
/// allocated fresh each time, via `Lowering::pap_env` -- so this isolates
/// the partial-application path's own per-iteration allocation cost. (A
/// partial application escapes into `caller`, so unlike
/// `capturing_closure_loop`'s directly called closure it is not lambda
/// lifted.) `compile_specialised` βv-reduces the whole spine -- `caller
/// (add acc) n` down to `add acc n` down to `acc+n` -- in 4
/// certificate-checked steps before the term reaches `try_compile`, so the
/// warm path this bench measures no longer allocates a partial
/// application's environment or dispatches through `caller` at all
/// (`RELATED_WORK.md` §37).
pub fn partial_application_loop(s: &mut TermStore) -> Hash {
    source(s, r"rec f n acc = if n <= 0 then acc else f (n - 1) ((\g z. g z) ((\x y. x + y) acc) n)")
}

/// `iterate` with `inc` baked in as the initial `g` and `n`/`x` baked in
/// too, so the whole term is closed (arity 0), running `iters` iterations
/// -- a closure-typed *parameter* threaded through every iteration and
/// called (`call_indirect`) each time, unlike `capturing_closure_loop`,
/// which creates a fresh closure every iteration instead of reusing one
/// passed in. Its own group runs it at the other two loop benchmarks'
/// depth (see `execution.rs`'s own comment on `capturing_closure_loop` for
/// why 20,000); `inconsistent_arity_loop_carried_parameter_loop`'s group
/// runs it shorter, as that group's baseline (see there for why).
pub fn closure_typed_loop_carried_parameter_loop(s: &mut TermStore, iters: i64) -> Hash {
    source(s, &format!(r"(rec f n g x = if n <= 0 then x else f (n - 1) g (g x)) ({iters}) (\y. y + 1) 0"))
}

/// Identical to `closure_typed_loop_carried_parameter_loop` -- same loop,
/// same `iters` iterations, same hot `g x` call each one -- with exactly
/// one addition: a dead (never reached, `1 < 0` is always false) extra
/// call site for `g` at arity 2. That's enough to make `g`
/// `ArityUse::Inconsistent`, which -- per compile.rs's own docs on
/// `Combinators::needs_generic_dispatch` -- switches the *whole* fragment
/// to curried dispatch, including the hot, live `g x` call the dead branch
/// has nothing to do with. This isolates exactly the cost
/// `RELATED_WORK.md`'s own design discussion flagged but never measured:
/// what a single, syntactically-present-but-never-taken inconsistent call
/// site costs an otherwise fast-path loop.
pub fn inconsistent_arity_loop_carried_parameter_loop(s: &mut TermStore, iters: i64) -> Hash {
    source(
        s,
        &format!(
            r"(rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)) ({iters}) (\y. y + 1) 0"
        ),
    )
}

/// Straight-line, no recursion.
pub fn straight_line(s: &mut TermStore) -> Hash {
    source(s, r"\a b. if a < b then a * 2 else b + 1")
}

/// Both `f` and `x` are its own parameters, no captures.
pub fn twice(s: &mut TermStore) -> Hash {
    source(s, r"\f x. f (f x)")
}

pub fn inc(s: &mut TermStore) -> Hash {
    source(s, r"\y. y + 1")
}

/// `twice inc 5`: non-capturing closures, no recursion (arity 0). The
/// higher-order demo term `main.rs` uses, and the baseline the other
/// closures-fragment shapes below are measured against.
pub fn twice_inc_5(s: &mut TermStore) -> Hash {
    source(s, r"(\f x. f (f x)) (\y. y + 1) 5")
}

/// A capturing closure, created and directly called
/// (`mk_clo_h`/`Env_n`/`build_env_expr`), unlike `twice_inc_5`'s
/// non-capturing one (`combinator_value`).
pub fn a_capturing_closure_call(s: &mut TermStore) -> Hash {
    source(s, r"\x. (\y. x + y) 5")
}

/// Partial application of a non-capturing literal lambda (`pap_ref`'s
/// simplest case).
pub fn a_pap_non_capturing(s: &mut TermStore) -> Hash {
    source(s, r"(\g. g 4) ((\x y. x + y) 3)")
}

/// Partial application of a *capturing* literal lambda (`\x y. x + y + z`
/// captures `z` and is under-applied by one argument), exercising
/// `pap_ref`'s leading-`Env_n` path on top of the plain PAP case above.
pub fn a_pap_capturing(s: &mut TermStore) -> Hash {
    source(s, r"\z. (\g2. g2 4) ((\x y. x + y + z) 3)")
}

/// Iterate a closure-typed parameter `n` times, starting at `x`:
/// tail-recursive, threading `g` (a `Clo_1`-typed parameter, called each
/// iteration) through the recursion unchanged -- the fragment
/// `prove_tail_recursive_universal`'s `param_types` extension covers.
/// Bare, unlike `closure_typed_loop_carried_parameter_loop`, which is
/// built for *execution*: the universal proof's cost depends only on the
/// function's own leaf/call structure, never on a concrete argument.
pub fn iterate(s: &mut TermStore) -> Hash {
    source(s, "rec f n g x = if n <= 0 then x else f (n - 1) g (g x)")
}

/// The loop of `proof::tests`'
/// `a_non_tail_self_call_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof`
/// without its dead call site (`if 1 < 0 then g x 999 else`), so `g` is
/// consistently classified here; fully saturated (arity 0) so `prove_closure_expr_instance` can be
/// called with `&[]` directly. `n = 20` sits well under
/// `DynBudget::recursion_depth`'s bound (`50`), giving this a real, if
/// modest, non-tail recursion depth without risking a decline.
pub fn non_tail_closure_carrying_recursion(s: &mut TermStore) -> Hash {
    source(s, r"(rec f n g x = if n <= 0 then x else 1 + f (n - 1) g (g x)) 20 (\y. y + 1) 0")
}

/// The loop of `proof::tests`'
/// `branching_non_tail_self_calls_carrying_an_inconsistently_classified_closure_parameter_get_a_per_instance_proof`
/// without its dead call site (`if 1 < 0 then g 0 999 else`), so `g` is
/// consistently classified here: a *branching* non-tail trace (two self-calls per interior leaf). Unlike
/// the single-call shape above, `DynBudget::recursion_depth` here bounds
/// the *total* number of self-calls across the whole trace (the budget
/// never refunds on return), which grows with the size of the recursion
/// tree, not its depth -- `n = 6` keeps that total (`2 * fib(n+1) - 1 =
/// 25`) under the shared bound of `50`.
pub fn branching_non_tail_closure_carrying_recursion(s: &mut TermStore) -> Hash {
    source(s, r"(rec f n g = if n <= 1 then g n else f (n - 1) g + f (n - 2) g) 6 (\y. y + 1)")
}

/// The canonical over-application shape: `f`'s own saturated call denotes
/// a further `Clo_1`, chosen by an `If` between two literal lambdas, then
/// the extra argument dispatches against it.
pub fn over_application_if_between_closures(s: &mut TermStore) -> Hash {
    source(s, r"(\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) 10 3 100")
}

/// The PAP-producing-root over-application shape: `f = \a. g a` denotes a
/// partial application of `g = \x y. x * 10 + y`, no branching at all,
/// then the extra argument completes `g`'s own call directly.
pub fn over_application_pap_producing_root(s: &mut TermStore) -> Hash {
    source(s, r"(\a. (\x y. x * 10 + y) a) 5 3")
}

/// Arithmetically trivial (both `If` branches are the identity, so the
/// argument always reduces to `n - 1` and the loop counts down to 0), but
/// puts an `If`-between-closures over-application in the self-call
/// argument, once per iteration, the way a real self-call argument built
/// from an over-application would.
pub fn tail_recursive_loop_with_if_between_closures_self_call_arg(s: &mut TermStore) -> Hash {
    source(s, r"rec f n = if n <= 0 then n else f ((\a b. if 0 < a then (\c. c) else (\c. c)) n n (n - 1))")
}

/// As `tail_recursive_loop_with_if_between_closures_self_call_arg`, with
/// a PAP-producing-root over-application (`(\a. (\p q. q) a) 0 x`, which
/// is `x`) in the self-call argument instead.
pub fn tail_recursive_loop_with_pap_producing_root_self_call_arg(s: &mut TermStore) -> Hash {
    source(s, r"rec f n = if n <= 0 then n else f ((\a. (\p q. q) a) 0 (n - 1))")
}

/// Every sample above, each in its own store; the two counted loops at
/// 150 iterations.
pub fn corpus() -> Vec<(&'static str, TermStore, Hash)> {
    let samples: [(&'static str, fn(&mut TermStore) -> Hash); 23] = [
        ("factorial", factorial),
        ("redundant_arithmetic_recursion", redundant_arithmetic_recursion),
        ("fib", fib),
        ("gcd", gcd),
        ("gcd_with_two_base_cases", gcd_with_two_base_cases),
        ("capturing_closure_loop", capturing_closure_loop),
        ("partial_application_loop", partial_application_loop),
        ("closure_typed_loop_carried_parameter_loop", |s| closure_typed_loop_carried_parameter_loop(s, 150)),
        ("inconsistent_arity_loop_carried_parameter_loop", |s| inconsistent_arity_loop_carried_parameter_loop(s, 150)),
        ("straight_line", straight_line),
        ("twice", twice),
        ("inc", inc),
        ("twice_inc_5", twice_inc_5),
        ("a_capturing_closure_call", a_capturing_closure_call),
        ("a_pap_non_capturing", a_pap_non_capturing),
        ("a_pap_capturing", a_pap_capturing),
        ("iterate", iterate),
        ("non_tail_closure_carrying_recursion", non_tail_closure_carrying_recursion),
        ("branching_non_tail_closure_carrying_recursion", branching_non_tail_closure_carrying_recursion),
        ("over_application_if_between_closures", over_application_if_between_closures),
        ("over_application_pap_producing_root", over_application_pap_producing_root),
        ("tail_recursive_loop_with_if_between_closures_self_call_arg", tail_recursive_loop_with_if_between_closures_self_call_arg),
        ("tail_recursive_loop_with_pap_producing_root_self_call_arg", tail_recursive_loop_with_pap_producing_root_self_call_arg),
    ];
    samples
        .into_iter()
        .map(|(name, build)| {
            let mut s = TermStore::new();
            let h = build(&mut s);
            (name, s, h)
        })
        .collect()
}

// Shapes that unit tests in two or three files share. Deliberately not in
// `corpus()`: the goldens, the rule census and the corpus-wide tests read
// the corpus, and these terms are only test inputs.

/// `f` called at two arities, and nothing more: no single type fits it.
pub fn inconsistent_arity_parameter(s: &mut TermStore) -> Hash {
    source(s, r"\f. f 1 + f 1 2")
}

/// A parameter called at two arities, given a 2-ary literal; the live call
/// (`f 1 2`) saturates it.
pub fn inconsistent_arity_saturating_instance(s: &mut TermStore) -> Hash {
    source(s, r"(\f. if 0 < 1 then f 1 2 else f 1) (\a b. a + b)")
}

/// As `inconsistent_arity_saturating_instance`, but the live call is `f 1`
/// and the literal is 1-ary.
pub fn inconsistent_arity_under_applying_instance(s: &mut TermStore) -> Hash {
    source(s, r"(\f. if 1 < 0 then f 1 2 else f 1) (\a. a + 100)")
}

/// As `inconsistent_arity_saturating_instance`, with the literal capturing
/// the outer parameter `k`.
pub fn inconsistent_arity_capturing_instance(s: &mut TermStore) -> Hash {
    source(s, r"\k. (\f. if 0 < 1 then f 1 2 else f 1) (\a b. k + a + b)")
}

/// As `inconsistent_arity_saturating_instance`, with the literal chosen at
/// run time by an `if` on the outer parameter.
pub fn inconsistent_arity_runtime_chosen_instance(s: &mut TermStore) -> Hash {
    source(s, r"\pick. (\f. if 0 < 1 then f 1 2 else f 1) (if 0 < pick then (\a b. a + b) else (\a b. a - b))")
}

/// `iterate` with one dead call site (`g x 999`, behind `1 < 0`) that
/// makes `g` inconsistently classified. Bare; applied, it is
/// `inconsistent_arity_loop_carried_parameter_loop`.
pub fn inconsistent_arity_iterate(s: &mut TermStore) -> Hash {
    source(s, "rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)")
}

/// A loop that creates, in its self-call argument, a closure capturing its
/// closure-typed loop parameter `g`.
pub fn iterate_creating_a_closure_over_g(s: &mut TermStore) -> Hash {
    source(s, r"rec f n g x = if n <= 0 then x else f (n - 1) g (g x + (\y. g y + 1) x)")
}

/// `factorial` bound by `let` and called at 10: a self-recursive
/// combinator used as a value.
pub fn let_bound_factorial_10(s: &mut TermStore) -> Hash {
    source(s, "let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10")
}

/// A literal lambda whose body picks between two closures over `x`, applied
/// to `x`, its result passed to `\g. g 5`.
pub fn calls_a_capturing_closure_picked_by_if(s: &mut TermStore) -> Hash {
    source(s, r"\x. (\g. g 5) ((\x. if 0 < x then (\y. x + y) else (\y. x - y)) x)")
}

/// A self-recursive combinator partially applied (one argument of two) and
/// completed through `\g. g 1`.
pub fn a_pap_of_a_self_recursive_combinator(s: &mut TermStore) -> Hash {
    source(s, r"(\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc)) 3)")
}

/// As `a_pap_of_a_self_recursive_combinator`, with the combinator capturing
/// the outer parameter `z`.
pub fn a_pap_of_a_capturing_self_recursive_combinator(s: &mut TermStore) -> Hash {
    source(s, r"\z. (\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc + z)) 3)")
}

/// `over_application_if_between_closures` with its three arguments as
/// parameters.
pub fn over_application_if_between_closures_of_params(s: &mut TermStore) -> Hash {
    source(s, r"\p q r. (\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) p q r")
}
