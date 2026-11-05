use super::*;
use crate::lang::eval;

#[test]
fn printing_a_free_variable_does_not_panic() {
    let mut store = TermStore::new();
    let v = store.intern(Term::Var(2));
    assert_eq!(print(&store, v), "#2");
}

#[test]
fn literal() {
    let mut s = TermStore::new();
    let h = parse(&mut s, "42").unwrap();
    assert_eq!(*s.resolve(h), Term::Lit(42));
}

#[test]
fn arithmetic_precedence() {
    // 1 + 2 * 3 should parse as 1 + (2 * 3), not (1 + 2) * 3.
    let mut s = TermStore::new();
    let parsed = parse(&mut s, "1 + 2 * 3").unwrap();

    let one = s.lit(1);
    let two = s.lit(2);
    let three = s.lit(3);
    let mul = s.prim(PrimOp::Mul, two, three);
    let expected = s.prim(PrimOp::Add, one, mul);

    assert_eq!(parsed, expected);
    assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 7);
}

#[test]
fn unary_minus_on_a_literal_evaluates_as_negation() {
    let mut s = TermStore::new();
    let parsed = parse(&mut s, "-5 + 3").unwrap();
    assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), -2);
}

#[test]
fn comparison_and_if() {
    let mut s = TermStore::new();
    let parsed = parse(&mut s, "if 1 < 2 then 10 else 20").unwrap();
    assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 10);
}

/// Parses `src` in a fresh `TermStore` and evaluates it with no
/// arguments -- avoids the `&s`/`&mut s` two-borrow conflict of
/// interleaving `parse`/`eval::apply_term` calls inline.
fn run(src: &str) -> i64 {
    let mut s = TermStore::new();
    let h = parse(&mut s, src).unwrap();
    eval::apply_term(&s, h, &[]).unwrap()
}

#[test]
fn greater_than_desugars_correctly() {
    // `a > b` desugars to `b < a` -- if the operand order were
    // swapped by mistake, `5 > 3` would come out false instead of true.
    assert_eq!(run("5 > 3"), 1);
    assert_eq!(run("3 > 5"), 0);
    assert_eq!(run("3 > 3"), 0);
}

#[test]
fn greater_or_equal_desugars_correctly() {
    assert_eq!(run("5 >= 3"), 1);
    assert_eq!(run("3 >= 5"), 0);
    assert_eq!(run("3 >= 3"), 1);
}

#[test]
fn not_equal_desugars_correctly() {
    assert_eq!(run("5 != 3"), 1);
    assert_eq!(run("3 != 3"), 0);
}

#[test]
fn logical_not_is_correct_for_any_truthy_operand_not_just_a_clean_bit() {
    assert_eq!(run("!0"), 1);
    assert_eq!(run("!1"), 0);
    // `5` is truthy (nonzero) even though it isn't a clean 0/1 --
    // `!a` desugaring to `1 - a` would wrongly give `-4` (still
    // truthy) here instead of `0`.
    assert_eq!(run("!5"), 0);
    assert_eq!(run("!(1 < 0)"), 1);
}

#[test]
fn logical_and_full_truth_table_and_short_circuits() {
    assert_eq!(run("0 && 0"), 0);
    assert_eq!(run("0 && 1"), 0);
    assert_eq!(run("1 && 0"), 0);
    assert_eq!(run("1 && 1"), 1);
    // Genuinely short-circuits: a falsy left operand means the right
    // side, which would otherwise error (division by zero), is never
    // evaluated.
    assert_eq!(run("0 && (1 / 0)"), 0);
}

#[test]
fn logical_or_full_truth_table_and_short_circuits() {
    assert_eq!(run("0 || 0"), 0);
    assert_eq!(run("0 || 1"), 1);
    assert_eq!(run("1 || 0"), 1);
    assert_eq!(run("1 || 1"), 1);
    assert_eq!(run("1 || (1 / 0)"), 1);
}

#[test]
fn logical_operator_precedence() {
    // `!` binds tighter than comparisons; `&&` binds tighter than
    // `||` -- `1 < 2 && 0 || !0` should parse as `((1<2) && 0) || (!0)`
    // = `0 || 1` = `1`; a wrong relative precedence would instead
    // group this to produce `0`.
    assert_eq!(run("1 < 2 && 0 || !0"), 1);
}

#[test]
fn bare_ampersand_or_pipe_is_a_lex_error() {
    let mut s = TermStore::new();
    assert!(parse(&mut s, "1 & 2").is_err());
    assert!(parse(&mut s, "1 | 2").is_err());
}

#[test]
fn lambda_application_and_last_param_is_innermost() {
    // \x y. x - y applied to (10, 3): x = 10 (first-applied, outer),
    // y = 3 (last-applied, inner) -- if the convention were backwards
    // this would come out -7 instead of 7.
    let mut s = TermStore::new();
    let f = parse(&mut s, "\\x y. x - y").unwrap();
    let ten = s.lit(10);
    let three = s.lit(3);
    let applied = s.app2(f, ten, three);
    assert_eq!(eval::apply_term(&s, applied, &[]).unwrap(), 7);
}

#[test]
fn let_binding() {
    let mut s = TermStore::new();
    let parsed = parse(&mut s, "let x = 5 in x + 1").unwrap();
    assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 6);
}

#[test]
fn shadowing_resolves_to_the_innermost_binder() {
    let mut s = TermStore::new();
    let f = parse(&mut s, "\\x. \\x. x").unwrap();
    let a = s.lit(1);
    let b = s.lit(2);
    let applied = s.app2(f, a, b);
    assert_eq!(eval::apply_term(&s, applied, &[]).unwrap(), 2);
}

#[test]
fn factorial_matches_the_hand_built_term_exactly() {
    // rec f n = if n <= 1 then 1 else n * f (n - 1) -- content-addressed
    // hashing means an *identical* structure, however it was built,
    // hashes identically; this is a strictly stronger check than "it
    // evaluates to the same answer".
    let mut s = TermStore::new();
    let parsed = parse(&mut s, "rec f n = if n <= 1 then 1 else n * f (n - 1)").unwrap();

    let n = s.var(0);
    let fv = s.var(1);
    let one = s.lit(1);
    let cond = s.prim(PrimOp::Le, n, one);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(fv, n_minus_1);
    let else_branch = s.prim(PrimOp::Mul, n, rec_call);
    let body = s.if_(cond, one, else_branch);
    let abs = s.abs(body);
    let hand_built = s.rec(abs);

    assert_eq!(parsed, hand_built);
    assert_eq!(eval::apply_term(&s, parsed, &[10]).unwrap(), 3628800);
}

#[test]
fn gcd_two_params_matches_the_hand_built_term_exactly() {
    let mut s = TermStore::new();
    let parsed = parse(&mut s, "rec f a b = if b == 0 then a else f b (a % b)").unwrap();

    let b = s.var(0);
    let a = s.var(1);
    let f = s.var(2);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Eq, b, zero);
    let a_mod_b = s.prim(PrimOp::Mod, a, b);
    let rec_call = s.app2(f, b, a_mod_b);
    let body = s.if_(cond, a, rec_call);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    let hand_built = s.rec(abs);

    assert_eq!(parsed, hand_built);
    assert_eq!(eval::apply_term(&s, parsed, &[48, 18]).unwrap(), 6);
}

#[test]
fn higher_order_let_chain_evaluates_like_the_inlined_sample() {
    // Mirrors samples::twice_inc_5: (twice inc) 5, but with
    // twice/inc each bound through their own let -- a behavioral
    // check, not a hash-equality one, since let-desugaring genuinely
    // builds a different term structure from the inlined
    // version (an extra App(Abs(..), ..) wrapper per let), not just a
    // different way of writing the same one.
    //
    // Interesting, honest finding: `let x = e1 in e2` desugars to
    // `App(Abs(e2), e1)`, so nesting a *second* let inside the
    // first's body makes the inner let's own `\y. ..` value reference
    // the outer let's binding by `Var`, not by name -- and when
    // compile.rs peels that inner lambda *standalone* (as it does for
    // any candidate combinator), that outer reference is exactly a
    // captured free variable. Nothing about the *source* looks like a
    // capturing closure; the capture is an artifact of two lets
    // nesting this way once desugared. compile.rs's closure
    // conversion (see its module docs) handles this correctly -- it
    // compiles and runs, not just falls back to the interpreter.
    //
    // A second, later finding, once `proof::prove_closure_expr_instance`
    // existed: this term's outer `inc` parameter is never actually
    // *called* anywhere in its own body (`inc` is only ever passed
    // along, as a plain value, to `twice`) -- so `param_types_for`
    // classifies it `None` (Int) for exactly the same reason it
    // classifies a genuinely inconsistent parameter that way (see
    // `shape::ArityUse`'s own docs): "never assigned a single
    // static arity", whether that's because it's never called at all
    // or because it's called at two disagreeing ones. `denote_closure`'s
    // own *universal* proof still declines this (the same `Int`
    // classification makes its own per-argument type check fail once
    // it sees `inc` is actually a `Clo`), but the per-instance
    // strategy's inlining doesn't care *why* a parameter was
    // classified `None` -- only that the concretely-supplied argument
    // disagrees with it -- so it picks this shape up too, entirely as
    // a side effect of the same mechanism built for the inconsistent-
    // arity case, not a separate one.
    let mut s = TermStore::new();
    let parsed = parse(&mut s, "let inc = \\y. y + 1 in let twice = \\f. \\x. f (f x) in twice inc 5").unwrap();
    assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 7);

    use crate::jit::JitEngine;
    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, parsed, &[]).unwrap(), 7);
    assert!(
        jit.is_kernel_verified(parsed),
        "prove_closure_expr_instance's own inlining covers this now, as a side effect of the inconsistent-arity mechanism -- see this test's own updated comment"
    );
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
}

#[test]
fn a_single_let_around_a_closure_still_compiles() {
    // let twice = \f. \x. f (f x) in twice (\y. y + 1) 5 -- inc is
    // inlined directly rather than separately let-bound, so twice's
    // own let-lambda doesn't reference anything outside its own
    // parameter range when peeled standalone: no accidental capture
    // (see the test above), and this does compile and get proven.
    let mut s = TermStore::new();
    let parsed = parse(&mut s, "let twice = \\f. \\x. f (f x) in twice (\\y. y + 1) 5").unwrap();
    assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 7);

    use crate::jit::JitEngine;
    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, parsed, &[]).unwrap(), 7);
    assert!(jit.is_kernel_verified(parsed));
}

#[test]
fn unbound_variable_is_a_parse_error() {
    let mut s = TermStore::new();
    let err = parse(&mut s, "x + 1").unwrap_err();
    assert!(err.message.contains("unbound variable"), "message was: {}", err.message);
}

#[test]
fn trailing_input_is_a_parse_error() {
    let mut s = TermStore::new();
    let err = parse(&mut s, "1 + 2)").unwrap_err();
    assert!(err.message.contains("Eof") || err.message.contains("expected"), "message was: {}", err.message);
}

#[test]
fn unclosed_paren_is_a_parse_error() {
    let mut s = TermStore::new();
    assert!(parse(&mut s, "(1 + 2").is_err());
}

#[test]
fn compiles_and_runs_through_the_jit_like_any_hand_built_term() {
    use crate::jit::JitEngine;

    let mut s = TermStore::new();
    let parsed = parse(&mut s, "rec f a b = if b == 0 then a else f b (a % b)").unwrap();
    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, parsed, &[270, 192]).unwrap(), 6);
    assert!(jit.is_kernel_verified(parsed));
}

/// `print(store, h)` reparses (into a fresh store) to the exact same
/// content hash -- a strictly stronger check than "prints something
/// plausible": content-addressing means this only holds if the printed
/// text really does denote the identical term structure.
fn assert_round_trips(store: &TermStore, h: Hash) {
    let text = print(store, h);
    let mut fresh = TermStore::new();
    let reparsed =
        parse(&mut fresh, &text).unwrap_or_else(|e| panic!("printed text failed to reparse: {text:?}\nerror: {e}"));
    assert_eq!(reparsed, h, "round-trip mismatch; printed: {text:?}");
}

#[test]
fn round_trips_arithmetic_with_mixed_precedence_and_right_nesting() {
    let mut s = TermStore::new();
    // 1 + 2 * 3 -- Mul binds tighter, no parens needed either way.
    let h1 = parse(&mut s, "1 + 2 * 3").unwrap();
    assert_round_trips(&s, h1);

    // A hand-built *right*-nested subtraction, which a left-associative
    // parser would never itself produce -- print must add parens
    // around the right operand to preserve the grouping, or this
    // would silently change from (a - (b - c)) to ((a - b) - c).
    let a = s.lit(10);
    let b = s.lit(3);
    let c = s.lit(2);
    let bc = s.prim(PrimOp::Sub, b, c);
    let right_nested = s.prim(PrimOp::Sub, a, bc);
    assert_round_trips(&s, right_nested);
    assert_eq!(eval::apply_term(&s, right_nested, &[]).unwrap(), 9); // 10 - (3 - 2)

    // A hand-built nested comparison -- parse_cmp doesn't chain, so
    // this needs parens around the inner comparison on either side.
    let one = s.lit(1);
    let two = s.lit(2);
    let three = s.lit(3);
    let inner_cmp = s.prim(PrimOp::Lt, one, two);
    let nested_cmp = s.prim(PrimOp::Eq, inner_cmp, three);
    assert_round_trips(&s, nested_cmp);
}

#[test]
fn round_trips_if_lambda_application_and_rec() {
    let mut s = TermStore::new();
    for src in [
        "if 1 < 2 then 10 else 20",
        "(\\x y. x - y) 10 3",
        "rec f n = if n <= 1 then 1 else n * f (n - 1)",
        "rec f a b = if b == 0 then a else f b (a % b)",
        "let inc = \\y. y + 1 in let twice = \\f. \\x. f (f x) in twice inc 5",
        "\\x. \\x. x", // shadowing
    ] {
        let h = parse(&mut s, src).unwrap_or_else(|e| panic!("fixture `{src}` failed to parse: {e}"));
        assert_round_trips(&s, h);
    }
}

#[test]
fn round_trips_an_application_argument_that_is_itself_an_application() {
    // f (g x) -- without parens around the argument, "f g x" would
    // parse as a 3-ary call to f instead.
    let mut s = TermStore::new();
    let h = parse(&mut s, "\\f. \\g. \\x. f (g x)").unwrap();
    assert_round_trips(&s, h);
}

#[test]
fn round_trips_a_zero_arity_rec() {
    // rec f = 5 -- unusual (no base case reachable via any argument,
    // out of compile.rs's fragment too -- see its own docs), but a
    // legitimate term this grammar can express and print needs to
    // handle it (zero Abs layers inside the Rec).
    let mut s = TermStore::new();
    let h = parse(&mut s, "rec f = 5").unwrap();
    assert_round_trips(&s, h);
}

#[test]
fn a_negative_literal_round_trips_exactly() {
    // `-n` folds into `Lit(-n)`, so a directly built negative Lit
    // reparses hash-identically -- including i64::MIN, whose magnitude
    // alone doesn't fit an i64.
    for n in [-5, i64::MIN] {
        let mut s = TermStore::new();
        let h = s.lit(n);
        let text = print(&s, h);
        assert_eq!(text, n.to_string());
        let mut fresh = TermStore::new();
        assert_eq!(parse(&mut fresh, &text).unwrap(), h);
    }
}

#[test]
fn unary_minus_folds_only_a_literal_operand() {
    let mut s = TermStore::new();
    let h = parse(&mut s, r"\x. -(3) - -x").unwrap();
    let (x, neg_three, zero) = (s.var(0), s.lit(-3), s.lit(0));
    let neg_x = s.prim(PrimOp::Sub, zero, x);
    let body = s.prim(PrimOp::Sub, neg_three, neg_x);
    assert_eq!(h, s.abs(body));
    // Folding matches `0 - n`'s wrapping Sub: `- -9223372036854775808`
    // is i64::MIN again, just as `0 - i64::MIN` evaluates to.
    assert_eq!(run("- -9223372036854775808"), i64::MIN);
    assert_eq!(run("0 - -9223372036854775808"), i64::MIN);
}

#[test]
fn out_of_range_literals_are_rejected() {
    let mut s = TermStore::new();
    assert!(parse(&mut s, "9223372036854775808").is_err());
    assert!(parse(&mut s, "-9223372036854775809").is_err());
    // `i64::MIN`'s magnitude isn't a literal in its own right, so it
    // can't head an application either.
    assert!(parse(&mut s, r"\x. -9223372036854775808 x").is_err());
}

#[test]
fn a_negative_literal_argument_is_parenthesised() {
    // `\v0. v0 -16` would reparse as the subtraction `v0 - 16`, not an
    // application -- the negative Lit must print as `(-16)`.
    let mut s = TermStore::new();
    let (v0, neg) = (s.var(0), s.lit(-16));
    let app = s.app(v0, neg);
    let h = s.abs(app);
    let text = print(&s, h);
    assert_eq!(text, "\\v0. v0 (-16)");

    let mut fresh = TermStore::new();
    assert_eq!(parse(&mut fresh, &text).unwrap(), h);

    // ... and as the function of an application, `-2 v0` would reparse
    // as `-(2 v0)`.
    let neg2 = s.lit(-2);
    let app = s.app(neg2, v0);
    let h = s.abs(app);
    assert_eq!(print(&s, h), "\\v0. (-2) v0");
}
