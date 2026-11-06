use super::*;

fn run(n: usize) {
    {
        let ad = add(n);
        let t0 = Instant::now();
        assert!(is_ok(typecheck(&bv_ty(n))));
        let tc0 = Instant::now();
        assert!(is_ok(typecheck(&ad)), "add typechecks at n={n}");
        println!("  typecheck add: {:?}", tc0.elapsed());
        let mask = if n == 64 { u64::MAX as u128 } else { (1u128 << n) - 1 };
        let cases: [(u128, u128); 4] = [(0, 0), (1, 1), (0xFF, 1), (0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210)];
        for (x, y) in cases {
            let (x, y) = (x & mask, y & mask);
            let got = app2(ad, lit(n, x), lit(n, y));
            let e0 = Instant::now();
            assert!(def_eq(&got, &lit(n, (x + y) & mask)), "add n={n} {x:#x}+{y:#x}");
            println!("  def_eq one add: {:?}", e0.elapsed());
            assert!(!def_eq(&got, &lit(n, (x + y + 1) & mask)), "must reject wrong sum n={n}");
        }
        println!("church bv n={n}: typecheck + 4 adds in {:?}", t0.elapsed());
    }
}

/// `table_app`'s memo (keyed on the truth table) gives one closed lambda for one truth table however the table is given, a
/// different one for another table, and the right values. (Hash-consing makes a rebuilt lambda pointer-equal too, so this
/// checks the key, not that the memo is hit; the speed is in docs/tier-cycle/, "Truth tables built once".)
#[test]
fn table_bodies_are_shared_per_truth_table() {
    tatic_kernel::scoped(|| {
        let head = |e: &Expr| match e.node() {
            tatic_kernel::Node::App(h, _) => h,
            _ => panic!("table_app is an application"),
        };
        let (a, b) = (table_app(&[t(), f()], &|v| v[0] != v[1]), table_app(&[f(), f()], &|v| v.iter().filter(|x| **x).count() == 1));
        assert!(tatic_kernel::node_key(&head(&head(&a))) == tatic_kernel::node_key(&head(&head(&b))));
        let c = table_app(&[t(), f()], &|v| v[0] && !v[1]);
        assert!(tatic_kernel::node_key(&head(&head(&a))) != tatic_kernel::node_key(&head(&head(&c))));
        for (e, want) in [(&a, true), (&b, false), (&c, true)] {
            assert_eq!(tatic_kernel::normalize(e), bit(want));
        }
    })
}

/// A cached gate is the table's node in its scope (a fresh build interns to the same children), shared between uses, and
/// rebuilt in a new scope, where the rebuild finds the copy `scoped` persisted from the first one.
#[test]
fn constants_are_built_once_per_generation() {
    let kids = |e: &Expr| match e.node() {
        tatic_kernel::Node::Lam(a, b) => (a, b),
        _ => panic!("and_ is a lambda"),
    };
    let fresh = || bool2(app3(var(4), var(2), app3(var(3), var(2), var(1), var(0)), var(0)));
    let first = tatic_kernel::scoped(|| {
        let (a, b, c) = (kids(&and_()), kids(&and_()), kids(&fresh()));
        assert!(tatic_kernel::node_key(&a.1) == tatic_kernel::node_key(&b.1) && tatic_kernel::node_key(&a.1) == tatic_kernel::node_key(&c.1));
        and_()
    });
    let first = kids(&first);
    tatic_kernel::scoped(|| {
        let (a, c) = (kids(&and_()), kids(&fresh()));
        assert!(tatic_kernel::node_key(&a.1) == tatic_kernel::node_key(&first.1), "rebuilt onto the persisted copy");
        assert!(tatic_kernel::node_key(&a.1) == tatic_kernel::node_key(&c.1) && a.1 == first.1);
    })
}

#[test]
pub fn church_bitvector_add_computes_by_conv_at_8_bits() {
    run(8);
}

#[test]
pub fn shared_carry_proof_checks_and_rejects_wrong_statements() {
    for n in [1usize, 2, 3, 4, 8] {
        for left in [false, true] {
            let (proof, stmt) = add_identity_proof_shared(n, 0, left, add_shared);
            ck(&format!("shared n={n} left={left}"), &proof, &stmt);
            let (proof1, stmt1) = add_identity_proof_shared(n, 1, left, add_shared);
            assert!(holds(&proof1, &stmt1).is_err(), "rhs 1 must be rejected at n={n} left={left}");
        }
    }
}

#[test]
pub fn add_zero_is_the_identity_on_a_symbolic_good_vector() {
    // per-bit lemma, stated against its own type
    let (p1, ty1) = bit_lemma(id(bool0(), xor(xor(var(0), f()), f()), var(0)), refl(t()), refl(f()));
    ck("sum bit", &p1, &ty1);
    // GoodBv is inhabited by canonical tuples (n = 2): good_mk = \a0 a1 ga0 ga1 P h. h a0 a1 ga0 ga1
    let n = 2;
    let good_mk = lam(bool0(), lam(bool0(), lam(app(good_bool(), var(1)), lam(app(good_bool(), var(1)),
        lam(arrow(bv_ty(n), sort(2)), lam(good_bv_step(n),
            app(app(app(app(var(0), var(5)), var(4)), var(3)), var(2))))))));
    let good_mk_ty = pi(bool0(), pi(bool0(), pi(app(good_bool(), var(1)), pi(app(good_bool(), var(1)),
        app(good_bv(n), church_tuple(&[var(3), var(2)]))))));
    ck("good_mk", &good_mk, &good_mk_ty);

    for n in [1usize, 2, 3, 4, 8] {
        let (proof, stmt) = add_zero_proof(n, 0);
        let t0 = Instant::now();
        ck(&format!("add x 0 = x at n={n}"), &proof, &stmt);
        println!("LEMMA n={n}: add x 0 = x checked in {:?}", t0.elapsed());
        // Mutation: the same proof must not prove `add x 1 = x`.
        let (proof1, stmt1) = add_zero_proof(n, 1);
        assert!(holds(&proof1, &stmt1).is_err(), "add x 1 = x must be rejected at n={n}");

        // Left identity: add zero x = x, by the same pattern with the operands swapped.
        let (lp, lstmt) = add_identity_proof(n, 0, true);
        let t1 = Instant::now();
        ck(&format!("add 0 x = x at n={n}"), &lp, &lstmt);
        println!("LEMMA n={n}: add 0 x = x checked in {:?}", t1.elapsed());
        let (lp1, lstmt1) = add_identity_proof(n, 1, true);
        assert!(holds(&lp1, &lstmt1).is_err(), "add 1 x = x must be rejected at n={n}");
    }
}

/// Scaling gate: the `add x 0 = x` proof's size (nodes counted once per allocation) must keep growing
/// by no more than 4.5x per doubling of the width, and stay under a fixed size at n=64. Both were
/// breached by an unshared shift in `cong_n`/`trans_proof` (design doc sections 54-56: 8x per doubling,
/// 1.58M nodes at n=64, against 3.0x and 288k now). A new proof builder that copies where it should
/// share fails here, not months later in a timing.
#[test]
pub fn add_zero_proof_size_scales_gently() {
    let size = |n: usize| tatic_kernel::term_sizes(&add_zero_proof(n, 0).0).0;
    let (s16, s32, s64) = (size(16), size(32), size(64));
    assert!(s32 as f64 / s16 as f64 <= 4.5, "n=16 -> 32: {s16} -> {s32} nodes");
    assert!(s64 as f64 / s32 as f64 <= 4.5, "n=32 -> 64: {s32} -> {s64} nodes");
    assert!(s64 <= 400_000, "n=64: {s64} nodes");
}

/// Build and check time of one lemma at the widths in `env` (comma separated, else `default`), each built and checked
/// inside one `scoped` call so the proof is interned as it is built (design doc section 69); `NO_SCOPE=1` is the
/// unscoped control. Prints `<label> n=..: build .., check .., proof dag=..`. `lemma_times.sh` (in the gitignored `scripts/experiments/`, kept on one machine)
/// runs the callers by name.
fn scaling_scoped(label: &str, env: &str, default: &str, build: impl Fn(usize) -> (Expr, Expr)) {
    let job = &Job::new(Setup::process());
    let ns: Vec<usize> = job.setup().var(env).unwrap_or(default).split(',').map(|v| v.trim().parse().unwrap()).collect();
    for n in ns {
        let body = || {
            let t0 = Instant::now();
            let (proof, stmt) = build(n);
            let built = t0.elapsed();
            let t1 = Instant::now();
            job.lemmas.ck(&format!("n={n}"), &proof, &stmt);
            println!("{label} n={n}: build {built:?}, check {:?}, proof dag={}", t1.elapsed(), tatic_kernel::term_sizes(&proof).0);
        };
        if job.setup().flag("NO_SCOPE", false) { body() } else { tatic_kernel::scoped(body) }
    }
}

/// `add x 0 = x` (`scaling_scoped`, widths `ZERO_NS`).
#[test]
#[ignore]
pub fn add_zero_lemma_scaling_scoped() {
    scaling_scoped("SCOPED", "ZERO_NS", "8,16,32,64,128,256,512", |n| add_zero_proof(n, 0));
}

#[test]
pub fn add_is_commutative_on_symbolic_good_vectors() {
    // n=16 guards the failure path: rejecting a false statement once printed its terms as trees, which
    // took minutes at this width (doc section 82).
    for n in [1usize, 2, 4, 16] {
        let (proof, stmt) = add_comm_proof(n, false);
        let t0 = Instant::now();
        ck(&format!("add x y = add y x at n={n}"), &proof, &stmt);
        println!("COMM n={n}: checked in {:?}", t0.elapsed());
        // Mutation: `add x y = add x x` must be rejected, by its own proof and by this one.
        let (wp, ws) = add_comm_proof(n, true);
        assert!(holds(&wp, &ws).is_err(), "wrong statement must be rejected at n={n}");
        assert!(holds(&proof, &ws).is_err(), "add x y = add x x must be rejected at n={n}");
    }
}

/// `add x y = add y x` (`scaling_scoped`, widths `COMM_NS`; design doc section 81).
#[test]
#[ignore]
pub fn add_comm_scaling_scoped() {
    scaling_scoped("COMM-SCOPED", "COMM_NS", "8,16,32,64", |n| add_comm_proof(n, false));
}

/// Probe: `add_shared x 0 = x` (carries let-bound in the statement), original `add` kept alongside.
#[test]
pub fn add_shared_zero_is_the_identity_on_a_symbolic_good_vector() {
    for n in [1usize, 2, 4, 8] {
        let (proof, stmt) = add_identity_proof_over(n, 0, false, add_shared);
        let t0 = Instant::now();
        ck(&format!("add_shared x 0 = x at n={n}"), &proof, &stmt);
        println!("SHARED n={n}: checked in {:?}", t0.elapsed());
        let (p1, s1) = add_identity_proof_over(n, 1, false, add_shared);
        assert!(holds(&p1, &s1).is_err(), "add_shared x 1 = x must be rejected at n={n}");
    }
}

/// One check of the universal `add x 0 = x` lemma for profiling (`SAMPLY.md`), with no timing: width `PROFILE_N`
/// (default 64); built and checked inside one `scoped` call with `PROFILE_SCOPED=1`; on a thread with a
/// `PROFILE_STACK_MB` stack when set (1024 keeps `grow` from ever needing a new segment). The profiling task passes no
/// environment, so these go in `<exe>.env` beside the profiled exe.
#[test]
#[ignore]
pub fn profile_add_zero() {
    let setup = Setup::process();
    let (n, scoped, stack_mb) = (setup.or("PROFILE_N", 64usize), setup.flag("PROFILE_SCOPED", false), setup.or("PROFILE_STACK_MB", 0usize));
    let run = move || {
        let check = || {
            let (proof, stmt) = add_zero_proof(n, 0);
            ck(&format!("profile n={n}"), &proof, &stmt)
        };
        if scoped { tatic_kernel::scoped(check) } else { check() }
    };
    if stack_mb == 0 { run() } else { std::thread::Builder::new().stack_size(stack_mb << 20).spawn(run).unwrap().join().unwrap() }
}

/// A large check must not churn stack segments: before `check_in` ran large checks on one big
/// segment, n=256 switched about 11,000 times and n=512 over 65,000 (doc sections 76 and 77), each a
/// Windows fiber. Ignored because n=256 is slow in a debug build; run with `--release`.
#[test]
#[ignore]
pub fn a_large_check_does_not_churn_stack_segments() {
    let (proof, stmt) = add_zero_proof(256, 0);
    let before = tatic_kernel::segment_switches();
    ck("n=256", &proof, &stmt);
    let switches = tatic_kernel::segment_switches() - before;
    println!("segment switches in the n=256 check: {switches}");
    assert!(switches < 100, "{switches} stack segment switches in one check");
}

#[test]
pub fn eq_bv_computes_on_literals() {
    for n in [1usize, 4, 8] {
        let ty = pi(bv_ty(n), pi(bv_ty(n), bool0()));
        ck("eq_bv type", &eq_bv(n), &ty.clone());
        let mask = low_bits(n);
        for (x, y) in [(0u128, 0u128), (1, 1), (mask, mask), (0, 1), (1, 0), (mask, 0), (0b101 & mask, 0b100 & mask)] {
            let got = app2(eq_bv(n), lit(n, x), lit(n, y));
            assert!(def_eq(&got, &bit(x == y)), "eq {x} {y} at n={n}");
        }
    }
}

#[test]
pub fn wrapping_div_min_by_minus_one_is_min() {
    for n in [1usize, 2, 4, 8, 32, 64] {
        tatic_kernel::scoped(|| {
            let (min, all) = (1u128 << (n - 1), if n == 128 { u128::MAX } else { (1u128 << n) - 1 });
            let (p, s) = wrap_div_min_proof(n, min, all);
            let t0 = Instant::now();
            ck(&format!("D3 at n={n}"), &p, &s);
            println!("D3 n={n}: checked in {:?}", t0.elapsed());
            // The guard must bite: other operands leave `r` alone, so the same proof is rejected.
            for (a, b) in [(min, all - 1), (min + 1, all), (0, all), (min, 0)] {
                if n >= 2 || (a, b) != (min, 0) {
                    let (p2, s2) = wrap_div_min_proof(n, a & all, b & all);
                    if (a & all, b & all) != (min, all) {
                        assert!(holds(&p2, &s2).is_err(), "D3 must fail for a={a:#x} b={b:#x} at n={n}");
                    }
                }
            }
        })
    }
}

#[test]
pub fn to_n_computes_on_good_literals() {
    for n in [1usize, 4, 8] {
        let ty = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), nat_ty()));
        let lift_ty = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), app(good_bv1(n), var(0))));
        ck("lift_good type", &lift_good(n), &lift_ty);
        ck("toN type", &to_n(n), &ty);
        let mask = low_bits(n);
        for v in [0u128, 1, 5 & mask, mask] {
            ck("good_lit", &good_lit(n, v), &app(good_bv(n), lit(n, v)));
            let got = app2(to_n(n), lit(n, v), good_lit(n, v));
            assert!(def_eq(&got, &nat_lit(v)), "toN {v} at n={n}");
            assert!(!def_eq(&got, &nat_lit(v + 1)), "toN {v}+1 must differ at n={n}");
        }
    }
}

/// D1/D2 on literals: the flag is `false` exactly for `b = 0` and `a = MIN, b = -1`.
#[test]
pub fn sdiv_flag_matches_the_spec_on_literals() {
    for n in [4usize, 8, 32, 64] {
        tatic_kernel::scoped(|| {
            let all = if n == 64 { u64::MAX as u128 } else { (1u128 << n) - 1 };
            let min = 1u128 << (n - 1);
            let samples = [0u128, 1, 2, min - 1, min, min + 1, all - 1, all];
            for &a in &samples {
                for &b in &samples {
                    let some = b != 0 && !(a == min && b == all);
                    let got = sdiv_some(n, lit(n, a), lit(n, b));
                    assert!(def_eq(&got, &bit(some)), "sdiv flag a={a:#x} b={b:#x} n={n}");
                    assert!(!def_eq(&got, &bit(!some)), "flag must not be both, a={a:#x} b={b:#x} n={n}");
                }
            }
        })
    }
}

#[test]
pub fn eq_with_a_literal_implies_equality_on_good_vectors() {
    // the bit lemmas, against their own types
    for (name, (p, ty)) in [
        ("and_l", and_peel(true)),
        ("and_r", and_peel(false)),
        ("good_and", good_and_lemma()),
        ("bit_t", bit_from_xnor(true)),
        ("bit_f", bit_from_xnor(false)),
        ("gx_t", good_xnor_lit(true)),
        ("gx_f", good_xnor_lit(false)),
    ] {
        ck(name, &p, &ty);
    }
    for n in [1usize, 2, 4, 8, 32] {
        tatic_kernel::scoped(|| {
            let mask = low_bits(n);
            for l in [0u128, 1, 0b1010 & mask, mask, 1u128 << (n - 1)] {
                let (p, s) = eq_lit_sound(n, l, l);
                let t0 = Instant::now();
                ck(&format!("H3 n={n} l={l:#x}"), &p, &s);
                if l == mask {
                    println!("H3 n={n}: checked in {:?}", t0.elapsed());
                }
                // Mutation: the conclusion `x = L'` for another literal must be rejected.
                let (p2, s2) = eq_lit_sound(n, l, l ^ 1);
                assert!(holds(&p2, &s2).is_err(), "x = L xor 1 must be rejected, n={n} l={l:#x}");
            }
        })
    }
}

#[test]
pub fn sdiv_is_none_on_the_guard_and_wrapper_keeps_r_otherwise() {
    for n in [1usize, 2, 4, 8, 32] {
        tatic_kernel::scoped(|| {
            let (_, all) = min_all(n);
            let (p, s) = sdiv_none_if_zero(n, 0);
            ck(&format!("D1 b=0, n={n}"), &p, &s);
            let (p1, s1) = sdiv_none_if_zero(n, 1);
            assert!(holds(&p1, &s1).is_err(), "b=1 must not give None, n={n}");
            let (p, s) = sdiv_none_on_overflow(n, all);
            ck(&format!("D1 overflow, n={n}"), &p, &s);
            let (p1, s1) = sdiv_none_on_overflow(n, all ^ 1);
            assert!(holds(&p1, &s1).is_err(), "b=-2 must not give None, n={n}");
            let t0 = Instant::now();
            let (p, s) = wrap_div_keeps_r(n, true);
            ck(&format!("D2 payload, n={n}"), &p, &s);
            println!("D2 payload n={n}: checked in {:?}", t0.elapsed());
            let (p1, s1) = wrap_div_keeps_r(n, false);
            assert!(holds(&p1, &s1).is_err(), "payload is not 0, n={n}");
        })
    }
}

#[test]
pub fn lowering_and_lt_witnesses_check() {
    let (p, ty) = lower_bit();
    ck("lower_bit", &p, &ty);
    for n in [1usize, 4] {
        let (p, ty) = lower_bv(n);
        ck(&format!("lower_bv n={n}"), &p, &ty);
        let (p, ty) = lower_bv_bits(n, false);
        assert!(holds(&p, &ty).is_err(), "unlowered bit witnesses must be rejected at n={n}");
        let (p, ty) = good_lt(n);
        ck(&format!("good_lt n={n}"), &p, &ty);
    }
}

#[test]
pub fn add_preserves_goodness() {
    for (name, op, tab) in [
        ("and", &(|a, b| and(a, b)) as &dyn Fn(Expr, Expr) -> Expr, &(|a: bool, b: bool| a && b) as &dyn Fn(bool, bool) -> bool),
        ("or", &|a, b| or(a, b), &|a, b| a || b),
        ("xor", &|a, b| xor(a, b), &|a, b| a != b),
    ] {
        let (p, ty) = good2(op, tab);
        ck(&format!("good_{name}"), &p, &ty);
    }
    // a wrong truth table must be rejected
    let (p, ty) = good2(&|a, b| and(a, b), &|a, b| a || b);
    assert!(holds(&p, &ty).is_err(), "and with the or table must be rejected");
    for n in [1usize, 2, 4, 8, 32] {
        tatic_kernel::scoped(|| {
            let (p, ty) = good_add(n);
            let t0 = Instant::now();
            ck(&format!("good_add n={n}"), &p, &ty);
            println!("GOOD-ADD n={n}: checked in {:?}", t0.elapsed());
        })
    }
}

/// Width scaling of the H3, D2 and `good_add` proofs (design doc section 89).
#[test]
#[ignore]
pub fn bv_lemma_scaling_h3_d2_good_add() {
    for n in [32usize, 64, 128] {
        tatic_kernel::scoped(|| {
            let l = (1u128 << (n - 1)) | 1;
            let l = if n >= 128 { l } else { l & ((1u128 << n) - 1) };
            let t0 = Instant::now();
            let (p, s) = eq_lit_sound(n, l, l);
            let built = t0.elapsed();
            let t1 = Instant::now();
            ck("H3", &p, &s);
            println!("SCALE-H3 n={n}: build {built:?}, check {:?}", t1.elapsed());
            let t0 = Instant::now();
            let (p, s) = wrap_div_keeps_r(n, true);
            let built = t0.elapsed();
            let t1 = Instant::now();
            ck("D2", &p, &s);
            println!("SCALE-D2 n={n}: build {built:?}, check {:?}", t1.elapsed());
            let t0 = Instant::now();
            let (p, s) = good_add(n);
            let built = t0.elapsed();
            let t1 = Instant::now();
            ck("good_add", &p, &s);
            println!("SCALE-GOODADD n={n}: build {built:?}, check {:?}", t1.elapsed());
        })
    }
}

#[test]
pub fn or_of_disjoint_vectors_adds_in_to_n() {
    for n in [2usize, 4, 8] {
        tatic_kernel::scoped(|| {
            for k in 1..n {
                let (p, s) = or_disjoint_proof(n, k, false);
                ck(&format!("H4 n={n} k={k}"), &p, &s);
                let (p2, s2) = or_disjoint_proof(n, k, true);
                assert!(holds(&p2, &s2).is_err(), "toN a + toN a must be rejected, n={n} k={k}");
            }
        })
    }
}

/// H4 by width, half-and-half split (design doc section 89). Stops at n=14: `nat_lit(2^i)` is unary, so the
/// terms double in size per bit; n=16 had not finished after 10 minutes.
#[test]
#[ignore]
pub fn or_disjoint_scaling() {
    for n in [6usize, 8, 10, 12, 14] {
        tatic_kernel::scoped(|| {
            let t0 = Instant::now();
            let (p, s) = or_disjoint_proof(n, n / 2, false);
            let built = t0.elapsed();
            let t1 = Instant::now();
            ck("H4", &p, &s);
            println!("SCALE-H4 n={n}: build {built:?}, check {:?}", t1.elapsed());
        })
    }
}

/// `add (add x y) z = add x (add y z)` (`scaling_scoped`, widths `ASSOC_NS`).
#[test]
#[ignore]
pub fn add_assoc_scaling_scoped() {
    scaling_scoped("ASSOC-SCOPED", "ASSOC_NS", "8,16,32,64", |n| add_assoc_proof(n, false));
}

#[test]
pub fn add_is_associative_on_symbolic_good_vectors() {
    for n in [1usize, 2, 4] {
        let (p, s) = add_assoc_proof(n, false);
        ck(&format!("add assoc n={n}"), &p, &s);
        let (p, s) = add_assoc_proof(n, true);
        assert!(holds(&p, &s).is_err(), "add (add x y) z = add x (add y y) must be rejected at n={n}");
    }
}

#[test]
pub fn add_of_x_and_not_x_is_all_ones() {
    for n in [1usize, 2, 4, 8] {
        let (p, s) = add_not_proof(n, false);
        ck(&format!("add x (xor x -1) = -1 at n={n}"), &p, &s);
        let (p, s) = add_not_proof(n, true);
        assert!(holds(&p, &s).is_err(), "... = 0 must be rejected at n={n}");
    }
}

// ---- Conjecture miner (design note 2026-10-01-search-execution-blend-design.md, sections 7-9).
// Terms over x, y (and z) are *run* on every tuple of n-bit literals by the kernel (`normalize`); terms with
// the same results are conjectured equal; each conjecture is then *checked*: by the matching library
// generator, or by a generic builder (`bitwise_law`) that has no template for the particular lemma.
