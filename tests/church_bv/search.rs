use super::rewrite::Node;
use super::*;
use hashbrown::HashSet;

/// The gate operations shared by the proof-term builder (`GoodOps`, over `Gb`) and plain evaluation (`Bools`).
pub trait Gates {
    type S: Clone;
    fn and(&self, x: &Self::S, y: &Self::S) -> Self::S;
    fn or(&self, x: &Self::S, y: &Self::S) -> Self::S;
    fn xor(&self, x: &Self::S, y: &Self::S) -> Self::S;
    fn konst(&self, b: bool) -> Self::S;
    fn sum3(&self, a: &Self::S, b: &Self::S, c: &Self::S) -> Self::S {
        let ab = self.xor(a, b);
        self.xor(&ab, c)
    }
    fn maj(&self, a: &Self::S, b: &Self::S, c: &Self::S) -> Self::S {
        let (ab, x) = (self.and(a, b), self.xor(a, b));
        let cx = self.and(c, &x);
        self.or(&ab, &cx)
    }
}

/// Plain Booleans: decides what `GoodOps` builds (`raw_table`), with no kernel terms.
pub struct Bools;

impl Gates for Bools {
    type S = bool;
    fn and(&self, x: &bool, y: &bool) -> bool {
        *x && *y
    }
    fn or(&self, x: &bool, y: &bool) -> bool {
        *x || *y
    }
    fn xor(&self, x: &bool, y: &bool) -> bool {
        x != y
    }
    fn konst(&self, b: bool) -> bool {
        b
    }
}

impl Gates for GoodOps {
    type S = Gb;
    fn and(&self, x: &Gb, y: &Gb) -> Gb {
        GoodOps::and(self, x, y)
    }
    fn or(&self, x: &Gb, y: &Gb) -> Gb {
        GoodOps::or(self, x, y)
    }
    fn xor(&self, x: &Gb, y: &Gb) -> Gb {
        GoodOps::xor(self, x, y)
    }
    fn konst(&self, b: bool) -> Gb {
        Gb { e: bit(b), g: good_bit(b) }
    }
}

/// `laws` reordered by a hash of the salt and each law's text (FNV-1a: deterministic across runs); salt 0 keeps the order.
pub fn shuffled(mut laws: Vec<(Term, Term)>, salt: usize) -> Vec<(Term, Term)> {
    if salt != 0 {
        laws.sort_by_cached_key(|(a, b)| format!("{salt}|{} = {}", a.show(), b.show()).bytes().fold(0xcbf29ce484222325u64, |h, c| (h ^ c as u64).wrapping_mul(0x100000001b3)));
    }
    laws
}

/// `shuffled`: a permutation of the given order, fixed per salt, different between salts; salt 0 keeps the order.
#[test]
pub fn shuffle_is_a_fixed_permutation() {
    let laws: Vec<(Term, Term)> = (0..50).map(|i| (Term::v(0), (0..i).fold(Term::v(1), |t, _| Term::op(ADD, t, Term::v(2))))).collect();
    let (sorted, a, a2, b) = (shuffled(laws.clone(), 0), shuffled(laws.clone(), 1), shuffled(laws.clone(), 1), shuffled(laws.clone(), 2));
    assert!(sorted == laws, "salt 0 keeps the order");
    assert!(a == a2, "same salt, same order");
    assert!(a != sorted && a != b);
    let set = |v: &Vec<(Term, Term)>| v.iter().cloned().collect::<hashbrown::HashSet<_>>();
    assert!(set(&a) == set(&sorted) && set(&b) == set(&sorted) && a.len() == sorted.len(), "a permutation");
}

/// The law-sequence variable `k` from `env` as a number, as `Setup::or` reads one (`job::parsed`).
pub fn num(env: &dyn Fn(&str) -> Option<String>, k: &str, d: usize) -> usize {
    crate::job::parsed(k, env(k).as_deref(), d)
}

#[test]
#[should_panic(expected = "RULEMINER_LAWS=25O")]
fn num_stops_at_an_unparsable_value() {
    num(&|_| Some("25O".to_string()), "RULEMINER_LAWS", 250);
}

/// Laws written as a law file (`driver::write_laws`) and read back (`read_named_laws`) are the same laws, names included:
/// the equal pairs of the binary operators over `leaves3`, at width 4.
#[test]
pub fn laws_survive_a_law_file() {
    let leaves = &leaves3();
    let pool: Vec<Term> = (0..6).flat_map(|o| leaves.iter().flat_map(move |&a| leaves.iter().map(move |&b| Term::op(o, a, b)))).collect();
    let laws: Vec<(String, Term, Term)> = pool_conjectures(pool, 4, STREAM_VARS, 60).into_iter().map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b)).collect();
    assert!(laws.len() >= 20, "{} laws", laws.len());
    let path = std::env::temp_dir().join(format!("law_file_{}.txt", std::process::id()));
    std::fs::write(&path, laws_text(&laws)).unwrap();
    let back = read_named_laws(path.to_str().unwrap());
    std::fs::remove_file(&path).unwrap();
    assert!(back == laws);
}

/// Laws as the `lhs = rhs` lines `read_laws` reads.
pub fn laws_text(laws: &[(String, Term, Term)]) -> String {
    laws.iter().map(|(_, a, b)| format!("{} = {}\n", a.show(), b.show())).collect()
}

/// `RULEMINER_GUARD`: from `clean` machine-free laws, score about `k`: every `step`-th, each standing for `clean / sampled` laws (weight in
/// units of 1000 per straggler), so the sample's net gain estimates the whole window's.
pub fn guard_plan(clean: usize, k: usize) -> (usize, i64) {
    let step = clean.div_ceil(k.max(1)).max(1);
    (step, 1000 * clean as i64 / clean.div_ceil(step).max(1) as i64)
}

#[test]
pub fn guard_plan_samples_and_weights() {
    assert_eq!(guard_plan(538, 120), (5, 4981)); // 108 laws sampled, each standing for about 5
    assert_eq!(guard_plan(100, 1000), (1, 1000)); // k above the count: every law, unit weight
    assert_eq!(guard_plan(100, 100), (1, 1000));
    let (step, w) = guard_plan(7, 3);
    assert_eq!((step, w), (3, 2333)); // laws 0, 3, 6: three laws for seven
    assert_eq!(guard_plan(0, 5).0, 1); // no clean laws: nothing to sample (the caller skips the guard)
}

/// Rule miner (search note section 36; parts in `miner.rs`, switches in `MinerConfig`): rewrite rules for the laws of
/// `RULEMINER_LAWFILE` that still need a whole-term machine proof under the rules in force (the "stragglers"); a
/// candidate is tried on the stragglers whose normalized terms contain an instance of its left side and scores by the
/// machine proofs it removes.
#[test]
#[ignore]
pub fn rule_miner() {
    crate::miner::run(&Setup::process())
}

/// `bitwise_law_k` dispatches to the per-position prover when a shift occurs: shl1 distributes over the bitwise
/// operators, and a false shift law fails to check.
#[test]
pub fn bitwise_law_proves_shift_laws_and_rejects_false_ones() {
    tatic::kernel::scoped(|| {
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let shl = |a: Term| op(6, a, Term::ZERO);
        let (x, y) = (Term::v(0), Term::v(1));
        for n in [3, 4] {
            for o in 1..=3 {
                let (p, s) = bitwise_law_k(n, 2, &shl(op(o, x, y)), &op(o, shl(x), shl(y)));
                ck("shl over bitwise", &p, &s);
            }
            let (p, s) = bitwise_law_k(n, 2, &shl(x), &x);
            assert!(holds(&p, &s).is_err(), "shl x = x must fail");
        }
    })
}

#[test]
pub fn notsub_rule_is_provable() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        for n in [3, 4] {
            let r = prove_rule(job, n, 1, &op(3, Term::v(0), Term::ONES), &op(4, Term::ONES, Term::v(0)));
            let (p, s) = r.expect("xor(x, -1) = sub(-1, x)");
            job.lemmas.ck("notsub", &p, &s);
        }
    })
}

/// `rewrite_law` closes `lt` laws: operands rewritten under the root, then congruence; a false law is refused.
#[test]
pub fn rewrite_law_proves_lt_laws() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let (x, y) = (Term::v(0), Term::v(1));
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let n = 4;
        for (name, t1, t2) in [
            ("lt (x + 0) y = lt x y", op(5, op(0, x, Term::ZERO), y), op(5, x, y)),
            ("lt (x + y) y = lt (y + x) y", op(5, op(0, x, y), y), op(5, op(0, y, x), y)),
            ("lt (x + y) (x + x) = lt (y + x) (x + x)", op(5, op(0, x, y), op(0, x, x)), op(5, op(0, y, x), op(0, x, x))),
        ] {
            let (p, s) = rewrite_law(job, n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no proof"));
            job.lemmas.ck(name, &p, &s);
        }
        assert!(rewrite_law(job, n, 2, &op(5, x, y), &op(5, y, x)).is_none());
    })
}

#[test]
pub fn lt_rules_with_constant_right_sides_are_provable() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let lt = |a: Term, b: Term| Term::op(LT, a, b);
        let n = 4;
        for k in [1usize, 2] {
            for (l, r) in [(lt(Term::ONES, Term::v(0)), lt(Term::ONES, Term::ONES)), (lt(Term::v(0), Term::v(0)), lt(Term::ONES, Term::ONES))] {
                let (p, s) = prove_rule(job, n, k, &l, &r).unwrap_or_else(|| panic!("k={k}: {} -> {}", l.show(), r.show()));
                job.lemmas.ck("lt rule", &p, &s);
            }
        }
    })
}

/// Two root rules close `lt(x, x) = lt(-1, x + y)` without a machine proof of the whole law.
#[test]
pub fn lt_root_rules_close_constant_false_laws() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let (x, y) = (Term::v(0), Term::v(1));
        let lt = |a: Term, b: Term| Term::op(LT, a, b);
        let add = |a: Term, b: Term| Term::op(ADD, a, b);
        let falsum = lt(Term::ONES, Term::ONES);
        let (r, spent) = job.spent(|job| job.with_mined(vec![(lt(x, x), falsum), (lt(Term::ONES, x), falsum)], |job| rewrite_law(job, 4, 2, &lt(x, x), &lt(Term::ONES, add(x, y)))));
        let fell = spent.fallbacks;
        let (p, s) = r.expect("proved");
        job.lemmas.ck("lt(x,x) = lt(-1, x+y)", &p, &s);
        assert_eq!(fell, 0, "no whole-term machine proof");
    })
}

#[test]
pub fn shr_mask_proves_root_shift_laws_over_arithmetic_and_rejects_false_ones() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = Term::v;
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let shr = |a: Term| op(7, a, Term::ZERO);
        let laws = [
            // closed argument: shr1 1 = 0
            (Term::ZERO, shr(op(4, Term::ZERO, Term::ONES))),
            // the arguments differ only in bit 0
            (shr(op(0, v(0), v(0))), shr(op(4, op(0, v(0), v(0)), Term::ONES))),
            (shr(op(0, op(4, v(0), Term::ONES), v(1))), shr(op(4, op(0, v(0), v(1)), Term::ONES))),
            // shifts the rewriter pushes down to atoms (`shr1 (1)`, `shr1 -1`): closed by the mask on the original sides
            (Term::ZERO, shr(op(1, op(4, Term::ZERO, Term::ONES), v(1)))),
            (shr(op(1, op(3, v(0), v(1)), v(0))), shr(op(1, v(0), op(3, v(1), Term::ONES)))),
        ];
        for n in [1usize, 3, 4] {
            for (l, r) in &laws {
                let (p, s) = rewrite_law(job, n, 2, l, r).unwrap_or_else(|| panic!("no proof: {} = {} at n={n}", l.show(), r.show()));
                job.lemmas.ck(&format!("{} = {} at n={n}", l.show(), r.show()), &p, &s);
            }
        }
        // not laws: the arguments differ above bit 0
        for (l, r) in [(shr(op(0, v(0), v(1))), shr(op(0, v(0), v(0)))), (Term::ZERO, shr(op(0, v(0), Term::ONES)))] {
            assert!(rewrite_law(job, 4, 2, &l, &r).is_none(), "{} = {}", l.show(), r.show());
        }
    })
}

/// Lemma ablation, end to end (search note section 51): the library lemmas `add x 0 = x`, `add 0 x = x`, `add x y = add y x`,
/// `add x ~x = -1` and associativity are proved from the statement alone, by the Moore-refinement encoding search inside
/// `add_tree_law` (no rewrite rule, no hand-written invariant), and checked by the kernel at several widths.
#[test]
pub fn encoding_search_rediscovers_library_lemmas_from_statements() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = Term::v;
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let laws = [
            ("add x 0 = x", 1, op(0, v(0), Term::ZERO), v(0)),
            ("add 0 x = x", 1, op(0, Term::ZERO, v(0)), v(0)),
            ("add x y = add y x", 2, op(0, v(0), v(1)), op(0, v(1), v(0))),
            ("add x ~x = -1", 1, op(0, v(0), op(3, v(0), Term::ONES)), Term::ONES),
            ("add (add x y) z = add x (add y z)", 3, op(0, op(0, v(0), v(1)), v(2)), op(0, v(0), op(0, v(1), v(2)))),
        ];
        for n in [1usize, 3, 4] {
            for (name, k, l, r) in &laws {
                let (p, s) = add_tree_law(job, n, *k, l, r).unwrap_or_else(|| panic!("no proof: {name} at n={n}"));
                job.lemmas.ck(&format!("{name} at n={n}"), &p, &s);
            }
        }
        // a non-law is refused
        assert!(add_tree_law(job, 4, 2, &op(0, v(0), v(1)), &op(0, v(0), v(0))).is_none());
    })
}

// ---- Variable multiplication as a circuit (search note section 58, goal D option b): `mul x y` as shift-and-add
// partial products over bits, `row_i[j] = y_i & x_(j-i)`, summed by ripple adders. Laws are proved per width by case
// analysis on all 2n input bits with `refl` leaves, so they are finite and compare circuits only (no numeric meaning).

/// `\a b. \C k. a C (\a_i.. b C (\b_i.. k out_0 .. out_(n-1)))` where `outs(a_bits, b_bits)` gives the output bits.
pub fn bits_circuit(n: usize, outs: BitsFn) -> Expr {
    let d = 4 + 2 * n;
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let a: Vec<Expr> = (0..n).map(|i| v(4 + i)).collect();
    let b: Vec<Expr> = (0..n).map(|i| v(4 + n + i)).collect();
    let mut body = apps(v(3), outs(&a, &b));
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(n), app2(var(3), var(1), inner)))))
}

pub fn add_rows(a: &[Expr], b: &[Expr]) -> Vec<Expr> {
    let mut carry = f();
    let mut sums = vec![];
    for i in 0..a.len() {
        let x = xor(a[i], b[i]);
        sums.push(xor(x, carry));
        carry = ripple_carry(false, a[i], b[i], carry, x);
    }
    sums
}

pub type BitsFn<'a> = &'a dyn Fn(&[Expr], &[Expr]) -> Vec<Expr>;
pub type KBitsFn<'a> = &'a dyn Fn(&[Vec<Expr>]) -> Vec<Expr>;

/// `Pi x y. GoodBv x -> GoodBv y -> Id(Bv_n, L x y, R x y)` where `L`, `R` are the circuits of the output-bit
/// functions `l`, `r` of the `n` bits of `x` and of `y`. Per output bit, case analysis on all `2n` input bits with
/// `refl` leaves, then `cong_n` and the witness eliminations (the skeleton of `bitwise_law_k`).
pub fn circuit_law(n: usize, l: BitsFn, r: BitsFn) -> (Expr, Expr) {
    let (lc, rc) = (bits_circuit(n, l), bits_circuit(n, r));
    circuit_law_k(n, 2, &|a| (app2(lc, a[0], a[1]), app2(rc, a[0], a[1])), &|v| l(&v[0], &v[1]), &|v| r(&v[0], &v[1]))
}

/// As `circuit_law` over `k` vectors: `sides(vectors)` builds the two sides from circuits, `l`/`r` give their output
/// bits from the `k` vectors' bits (the sides must reduce to those bits by conversion).
pub fn circuit_law_k(n: usize, k: usize, sides: &dyn Fn(&[Expr]) -> (Expr, Expr), l: KBitsFn, r: KBitsFn) -> (Expr, Expr) {
    let split = |v: &[Expr]| -> Vec<Vec<Expr>> { (0..k).map(|i| v[i * n..(i + 1) * n].to_vec()).collect() };
    let lemmas: Vec<Expr> = (0..n)
        .map(|j| {
            lemma_n(
                k * n,
                &|v| id(bool0(), l(&split(v))[j], r(&split(v))[j]),
                &|b| refl(l(&split(&b.iter().map(|x| bit(*x)).collect::<Vec<_>>()))[j]),
            )
            .0
        })
        .collect();
    k_var_law_to(n, k, &bv_ty(n), sides, &|bits, goods| {
        let vb: Vec<Vec<Expr>> = (0..k).map(|v| (0..n).map(|i| bits(v, i)).collect()).collect();
        let (s1, s2) = (l(&vb), r(&vb));
        let witnesses: Vec<Expr> = (0..k).flat_map(|v| (0..n).map(move |i| (v, i))).map(|(v, i)| goods(v, i)).collect();
        let e = (0..n).map(|j| apps(lemmas[j], vb.iter().flatten().cloned().chain(witnesses.iter().cloned()).collect())).collect();
        let fbody = bits_to_bv(n);
        cong_n(&bool0(), &bv_ty(n), &fbody, &s1, &s2, e)
    })
}

pub fn mul_bits(n: usize, x: &[Expr], y: &[Expr]) -> Vec<Expr> {
    let row = |i: usize| -> Vec<Expr> { (0..n).map(|j| if j < i { f() } else { and(y[i], x[j - i]) }).collect() };
    (1..n).fold(row(0), |acc, i| add_rows(&acc, &row(i)))
}
pub fn const_bits(n: usize, c: u128) -> Vec<Expr> {
    (0..n).map(|i| bit((c >> i) & 1 == 1)).collect()
}

#[test]
pub fn mul_circuit_laws_by_case_analysis_and_false_ones_rejected() {
    for n in [2usize, 3, 4] {
        tatic::kernel::scoped(|| {
            let m = |x: &[Expr], y: &[Expr]| mul_bits(n, x, y);
            let t0 = Instant::now();
            let laws: Vec<(&str, Box<BitsDyn>, Box<BitsDyn>)> = vec![
                ("mul x y = mul y x", Box::new(move |x, y| mul_bits(n, x, y)), Box::new(move |x, y| mul_bits(n, y, x))),
                ("mul x 1 = x", Box::new(move |x, _| mul_bits(n, x, &const_bits(n, 1))), Box::new(|x, _| x.to_vec())),
                ("mul x 0 = 0", Box::new(move |x, _| mul_bits(n, x, &const_bits(n, 0))), Box::new(move |_, _| const_bits(n, 0))),
                ("mul x 2 = add x x", Box::new(move |x, _| mul_bits(n, x, &const_bits(n, 2))), Box::new(|x, _| add_rows(x, x))),
            ];
            for (name, l, r) in &laws {
                let (p, s) = circuit_law(n, &**l, &**r);
                ck(&format!("{name} n={n}"), &p, &s);
                println!("MUL {name} n={n}: {:?}", t0.elapsed());
            }
            let (p, s) = circuit_law(n, &m, &|x, y| add_rows(x, y));
            assert!(holds(&p, &s).is_err(), "mul = add must be rejected, n={n}");
        })
    }
}

/// Three-vector laws: `mul` distributes over `add`, and is associative (circuits composed from the two-vector ones).
#[test]
pub fn mul_circuit_three_vector_laws() {
    for n in [2usize, 3] {
        tatic::kernel::scoped(|| {
            let (mc, ac) = (bits_circuit(n, &move |x, y| mul_bits(n, x, y)), bits_circuit(n, &|x, y| add_rows(x, y)));
            let t0 = Instant::now();
            let dist = circuit_law_k(
                n,
                3,
                &|a| (app2(mc, a[0], app2(ac, a[1], a[2])), app2(ac, app2(mc, a[0], a[1]), app2(mc, a[0], a[2]))),
                &|v| mul_bits(n, &v[0], &add_rows(&v[1], &v[2])),
                &|v| add_rows(&mul_bits(n, &v[0], &v[1]), &mul_bits(n, &v[0], &v[2])),
            );
            ck(&format!("mul distributes n={n}"), &dist.0, &dist.1);
            let assoc = circuit_law_k(
                n,
                3,
                &|a| (app2(mc, app2(mc, a[0], a[1]), a[2]), app2(mc, a[0], app2(mc, a[1], a[2]))),
                &|v| mul_bits(n, &mul_bits(n, &v[0], &v[1]), &v[2]),
                &|v| mul_bits(n, &v[0], &mul_bits(n, &v[1], &v[2])),
            );
            ck(&format!("mul assoc n={n}"), &assoc.0, &assoc.1);
            println!("MUL3 n={n}: {:?}", t0.elapsed());
            // false: x * (y + z) = x * y + z
            let bad = circuit_law_k(
                n,
                3,
                &|a| (app2(mc, a[0], app2(ac, a[1], a[2])), app2(ac, app2(mc, a[0], a[1]), a[2])),
                &|v| mul_bits(n, &v[0], &add_rows(&v[1], &v[2])),
                &|v| add_rows(&mul_bits(n, &v[0], &v[1]), &v[2]),
            );
            assert!(holds(&bad.0, &bad.1).is_err(), "false distributivity must be rejected, n={n}");
        })
    }
}

/// Whether `l -> r` decreases in the rule order and is provable at widths 3 and 4 (the admission test for a rule).
pub fn rule_admissible(job: &mut Job, l: &Term, r: &Term) -> bool {
    rule_order_ok(l, r) && [3usize, 4].iter().all(|&n| prove_rule(job, n, l.max_var().max(r.max_var()) + 1, l, r).is_some())
}

#[test]
pub fn promoted_rules_are_ordered_and_provable() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        for (l, r) in promoted_rules() {
            assert_eq!(parse_term(&l.show()).show(), l.show());
            assert!(rule_admissible(job, l, r), "{} -> {} is not decreasing in the rule order or not provable at widths 3 and 4", l.show(), r.show());
        }
    })
}

/// The admission test refuses wrong rules: every promoted rule with its right side replaced by another promoted rule's
/// right side over the same variables (so it stays well-formed and, where the order allows, decreasing) is refused unless
/// it happens to be a true law.
#[test]
pub fn rule_admission_refuses_wrong_rules() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let rs = promoted_rules();
        let (mut refused, mut tried) = (0, 0);
        for (l, _) in rs {
            for (_, r) in rs {
                let vars = |t: &Term| (0..8).filter(|v| t.has_var(*v)).collect::<Vec<_>>();
                if vars(r).iter().any(|v| !vars(l).contains(v)) || l.size() <= r.size() {
                    continue;
                }
                tried += 1;
                let true_law = l.is_law(r, 2);
                if !true_law {
                    assert!(!rule_admissible(job, l, r), "wrong rule admitted: {} -> {}", l.show(), r.show());
                    refused += 1;
                }
            }
        }
        println!("ADMISSION {refused} wrong rules refused of {tried} tried");
        assert!(refused > 50, "too few wrong rules exercised: {refused}");
    })
}

/// `show_cmp` is the order of the `show()` text, on every pair of the class table's first 2000 representatives in that
/// order, constants and variables included.
#[test]
pub fn show_cmp_is_the_text_order() {
    let mut reps: Vec<Term> = crate::classes::Classes::get().reps().collect();
    reps.sort_by_cached_key(|t| t.show());
    let ts: Vec<Term> = reps.into_iter().take(2000).chain([Term::ZERO, Term::ONES, Term::v(0), Term::v(2)]).collect();
    for a in &ts {
        for b in &ts {
            assert_eq!(a.show_cmp(b), a.show().cmp(&b.show()), "{} vs {}", a.show(), b.show());
        }
    }
}

/// The rotation (spec decision 8): every set of two and three of the seven bit-vector operators, none with `lt`.
#[test]
pub fn stream_sets_are_the_pairs_and_triples() {
    let sets = stream_sets();
    assert_eq!(sets.len(), 56);
    assert_eq!(sets.iter().filter(|s| s.len() == 2).count(), 21);
    assert!(sets.iter().all(|s| (2..=3).contains(&s.len()) && !s.contains(&LT)));
}

/// Review Focus 3: a stream is the same laws in the same order on every call (two direct calls, not the memo); another
/// salt gives other laws; every law's sides use only the set's operators, the table leaves it open, and it agrees on
/// the 4096 width-8 inputs.
#[test]
pub fn stream_laws_are_deterministic_and_open() {
    let ops = [ADD, SHR1];
    let (a, b) = (stream_laws(&ops, 1, 2000, 2), stream_laws(&ops, 1, 2000, 2));
    assert!(a.len() > 20, "{} laws", a.len());
    assert!(a == b, "same salt, other laws or order");
    assert!(a != stream_laws(&ops, 2, 2000, 2), "another salt, the same laws");
    fn within(t: &Term, ops: &[usize]) -> bool {
        match *t.node() {
            Node::Op(o, x, y) => ops.contains(&o) && within(&x, ops) && within(&y, ops),
            _ => true,
        }
    }
    let c = crate::classes::Classes::get();
    let job = &mut Job::new(Setup::process());
    let mut r8 = width8();
    tatic::kernel::scoped(|| {
        for (x, y) in &a {
            assert!(within(x, &ops) && within(y, &ops), "{} = {}", x.show(), y.show());
            assert!(c.normalize(job, 4, 3, x).0 != c.normalize(job, 4, 3, y).0, "closed: {} = {}", x.show(), y.show());
            let vx = r8.values(x).to_vec();
            assert_eq!(vx, r8.values(y).to_vec(), "{} = {}", x.show(), y.show());
        }
    });
}

/// Phases are residue classes at `STREAM_STRIDE`, windowed by skip and count.
#[test]
pub fn residue_takes_a_phase_window() {
    let seq: Vec<(Term, Term)> = (0..40).map(|i| (Term::v(0), (0..i).fold(Term::v(1), |t, _| Term::op(ADD, t, Term::v(2))))).collect();
    let at = |w: Vec<(Term, Term)>| w.iter().map(|l| seq.iter().position(|s| s == l).unwrap()).collect::<Vec<_>>();
    assert_eq!(at(residue(&seq, 1, 0, 3)), [1, 5, 9]);
    assert_eq!(at(residue(&seq, 2, 1, 2)), [6, 10]);
    assert_eq!(at(residue(&seq, 3, 9, 5)), [39]);
}

/// The streams' operator sets (spec decision 8): every set of two and three of the seven bit-vector operators, in the
/// order of their bit masks over `[ADD, AND, OR, XOR, SUB, SHL1, SHR1]` (as `docs/runs/2026-10-23/scripts/mix_streams.sh`).
pub fn stream_sets() -> Vec<Vec<usize>> {
    let ops = [ADD, AND, OR, XOR, SUB, SHL1, SHR1];
    (1u32..128).filter(|m| matches!(m.count_ones(), 2 | 3)).map(|m| (0..7).filter(|i| m >> i & 1 == 1).map(|i| ops[i]).collect()).collect()
}

/// Terms grown per level of a stream (the probe's budget, docs/tier-cycle.md "Triples match pairs per grown term").
pub const STREAM_BUDGET: usize = 20000;

/// The stream laws' variables (`x`, `y`, `z`).
pub const STREAM_VARS: usize = 3;
/// Growth levels of a stream.
pub const STREAM_LEVELS: usize = 2;
/// Phases of the stream sequence: phase 0 feeds the mines' extras, 1-3 the loops (spec §9).
pub const STREAM_STRIDE: usize = 4;

/// The 4096 pseudo-random width-8 inputs an open law must agree on (the probe's): width 4 only conjectured it.
fn width8() -> ValueMemo<u8> {
    let mut seed = 0x6a09_e667_f3bc_c908u128;
    let vars: Vec<Box<[u8]>> = (0..3)
        .map(|_| {
            (0..4096)
                .map(|_| {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    (seed >> 40) as u8
                })
                .collect()
        })
        .collect();
    ValueMemo::new(8, 4096, vars)
}

/// One stream (spec §9; the probe `open_law_counts`, `docs/runs/2026-10-23/patches/open_law_counts_table.patch`): seeds
/// are the class table's representatives whose operators lie in `ops`; `levels` times, one leaf of a term is grown into
/// one of the seeds' operators over two leaves (`shl1` and `shr1` over one), padding dropped, about `budget` terms per
/// level drawn by `salt`. Laws are grouped by width-4 values as `pool_conjectures` does, have a grown side, use all three
/// variables, and are shuffled by `salt`; kept when the table leaves them open (normal forms differ) and they agree on
/// `width8`'s inputs. Prints the laws kept and refuted.
pub fn stream_laws(ops: &[usize], salt: usize, budget: usize, levels: usize) -> Vec<(Term, Term)> {
    let c = crate::classes::Classes::get();
    fn within(t: Term, ops: &[usize]) -> bool {
        match *t.node() {
            Node::Op(o, a, b) => ops.contains(&o) && within(a, ops) && within(b, ops),
            _ => true,
        }
    }
    let mut seeds: Vec<Term> = c.reps().filter(|t| within(*t, ops)).collect();
    seeds.sort_by_cached_key(|t| t.show());
    fn ops_of(t: Term, out: &mut std::collections::BTreeSet<usize>) {
        if let Node::Op(o, a, b) = *t.node() {
            out.insert(o);
            ops_of(a, out);
            ops_of(b, out);
        }
    }
    // the leaf positions of a term (a shift's second operand is not one), and the term with leaf `k` replaced by `g`
    fn leaf_count(t: Term) -> usize {
        match *t.node() {
            Node::Op(SHL1 | SHR1, a, _) => leaf_count(a),
            Node::Op(_, a, b) => leaf_count(a) + leaf_count(b),
            _ => 1,
        }
    }
    fn replaced(t: Term, k: &mut Option<usize>, g: Term) -> Term {
        match *t.node() {
            Node::Op(o @ (SHL1 | SHR1), a, b) => Term::op(o, replaced(a, k, g), b),
            Node::Op(o, a, b) => {
                let a = replaced(a, k, g);
                Term::op(o, a, replaced(b, k, g))
            }
            _ => match *k {
                Some(0) => {
                    *k = None;
                    g
                }
                Some(i) => {
                    *k = Some(i - 1);
                    t
                }
                None => t,
            },
        }
    }
    let mut grown_ops = std::collections::BTreeSet::new();
    seeds.iter().for_each(|t| ops_of(*t, &mut grown_ops));
    let leaves = &leaves3();
    let mut memo = ValueMemo::exhaustive(4, 3);
    let leaf_values: Vec<Vec<u8>> = leaves.iter().map(|l| memo.values(l).to_vec()).collect();
    let grow: Vec<Term> = grown_ops
        .iter()
        .flat_map(|&o| if o == SHL1 || o == SHR1 { leaves.iter().map(|a| mk(o, a, &Term::ZERO)).collect::<Vec<_>>() } else { leaves.iter().flat_map(|a| leaves.iter().map(move |b| mk(o, a, b))).collect() })
        .filter(|g| !leaf_values.contains(&memo.values(g).to_vec()))
        .collect();
    let mut level: hashbrown::HashMap<Term, usize> = seeds.iter().map(|t| (*t, 0)).collect();
    let (mut base, mut i) = (seeds.clone(), 0u64);
    for l in 1..=levels {
        let total: usize = base.iter().map(|t| leaf_count(*t)).sum::<usize>() * grow.len();
        let mut next = vec![];
        for t in &base {
            for p in 0..leaf_count(*t) {
                for g in &grow {
                    i += 1;
                    if (tatic::rng::mix64(i ^ tatic::rng::mix64(salt as u64 + 13 * l as u64)) % total.max(1) as u64) < budget as u64 {
                        let w = replaced(*t, &mut Some(p), *g);
                        if !level.contains_key(&w) {
                            level.insert(w, l);
                            next.push(w);
                        }
                    }
                }
            }
        }
        base = next;
    }
    // sorted, so the order owes nothing to the map's
    let mut terms: Vec<Term> = level.keys().cloned().collect();
    terms.sort_by_cached_key(|t| (level[t], t.show()));
    let laws: Vec<(Term, Term)> =
        pool_conjectures(terms, 4, 3, 0).into_iter().filter(|(a, b)| level[a].max(level[b]) > 0 && (0..3).all(|v| a.has_var(v) || b.has_var(v))).collect();
    let job = &mut Job::new(Setup::process());
    let mut r8 = width8();
    let (mut out, mut refuted) = (vec![], 0usize);
    tatic::kernel::scoped(|| {
        for (a, b) in shuffled(laws, salt) {
            if c.normalize(job, 4, 3, &a).0 == c.normalize(job, 4, 3, &b).0 {
                continue;
            }
            let va = r8.values(&a).to_vec();
            if va != r8.values(&b) {
                refuted += 1;
                continue;
            }
            out.push((a, b));
        }
    });
    let names: Vec<&str> = ops.iter().map(|o| OP_INFO[*o].name).collect();
    println!("STREAM {} salt {salt}: {} open laws, {refuted} refuted at width 8", names.join(","), out.len());
    out
}

/// The law sequence for `salt` with the table's representatives grown `levels` times (spec §9; the loops use
/// `STREAM_LEVELS`): the 56 streams (`stream_sets`, `STREAM_BUDGET`) interleaved round-robin, a law kept at its first
/// appearance. Built once per process, salt and growth count, on `STREAM_THREADS` threads (default 4, so three gate
/// processes fill the 12-core cap; clamped to 1..=12; 4 threads: 5.4 s and 2.8 GB against 15.4 s and 1.4 GB serial,
/// run `2026-10-27-cu18-seqmem-b`).
pub fn stream_sequence(salt: usize, levels: usize) -> std::sync::Arc<Vec<(Term, Term)>> {
    static MEMO: crate::task::SharedMemo<(usize, usize), std::sync::Arc<Vec<(Term, Term)>>> = crate::task::SharedMemo::new();
    let threads = Setup::process().or("STREAM_THREADS", 4).clamp(1, 12);
    MEMO.with((salt, levels), || std::sync::Arc::new(build_sequence(salt, STREAM_BUDGET, levels, threads)), |s| s.clone())
}

/// `stream_sequence`'s build: the streams on `threads` threads, each taking the next stream when free (their costs differ),
/// merged by stream index. A stream is a pure function of its operators, salt, budget and growth count, so the sequence
/// is the same at any thread count (`a_stream_sequence_is_the_same_on_any_thread_count`).
fn build_sequence(salt: usize, budget: usize, levels: usize, threads: usize) -> Vec<(Term, Term)> {
    let t0 = std::time::Instant::now();
    let sets = stream_sets();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let mut streams: Vec<Vec<(Term, Term)>> = vec![vec![]; sets.len()];
    std::thread::scope(|sc| {
        let worker = || {
            let mut built = vec![];
            loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(ops) = sets.get(i) else { break built };
                built.push((i, stream_laws(ops, salt, budget, levels)));
            }
        };
        let handles: Vec<_> = (0..threads.min(sets.len())).map(|_| std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, worker).unwrap()).collect();
        for h in handles {
            for (i, s) in h.join().unwrap() {
                streams[i] = s;
            }
        }
    });
    let (mut seen, mut seq) = (HashSet::new(), vec![]);
    for i in 0..streams.iter().map(Vec::len).max().unwrap_or(0) {
        for s in &streams {
            if let Some(l) = s.get(i) {
                if seen.insert(*l) {
                    seq.push(*l);
                }
            }
        }
    }
    println!("STREAMS salt {salt}, {levels} growths: {} laws from {} streams in {:.1}s on {threads} threads", seq.len(), streams.len(), t0.elapsed().as_secs_f64());
    seq
}

/// The streams built on one thread and on four give one sequence (at a smaller budget than the loops'). The four-thread
/// build goes first, so the shared memos it reads (`VERDICTS`, `TREE_ENCS`, the class lookups) start as cold as the
/// process allows, and an order-dependent fill would show.
#[test]
fn a_stream_sequence_is_the_same_on_any_thread_count() {
    let parallel = build_sequence(1, 2000, 2, 4);
    assert!(parallel == build_sequence(1, 2000, 2, 1));
}

/// Phase `phase`'s window of a sequence: its residue class at `STREAM_STRIDE`, `laws` of them from `skip`.
pub fn residue(seq: &[(Term, Term)], phase: usize, skip: usize, laws: usize) -> Vec<(Term, Term)> {
    seq.iter().skip(phase).step_by(STREAM_STRIDE).skip(skip).take(laws).cloned().collect()
}

/// Builds `stream_sequence(STREAMS_SALT)` (default 1) and prints its size and time: what a sweep pays once (spec §9, Risks).
#[test]
#[ignore]
pub fn stream_sequence_cost() {
    let salt = Setup::process().or("STREAMS_SALT", 1usize);
    let seq = stream_sequence(salt, STREAM_LEVELS);
    println!("SEQUENCE salt {salt}: {} laws; phase 1 window of 300: {}", seq.len(), residue(&seq, 1, 0, 300).len());
}

/// A law's twin key (the law generator's twin filter, docs/superpowers/specs/2026-10-17-law-generator-design.md §1; on
/// the class table since docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md §6): the least `a = b` text,
/// over the six renamings of x, y, z and both side orders, of the law renamed and then each side's children made
/// canonical (renaming first, since a representative is not preserved by renaming). A side's root is kept: canonicalizing
/// it too would make every law trivial whose sides are of one class, which every true law within the table's size is.
/// `None` if the sides are then one term (the law is trivial).
pub fn twin_key(a: &Term, b: &Term) -> Option<String> {
    let c = crate::classes::Classes::get();
    let side = |t: Term| match *t.node() {
        Node::Op(o, x, y) => Term::op(o, c.canonical(&x), c.canonical(&y)),
        _ => t,
    };
    if side(*a) == side(*b) {
        return None;
    }
    const PERMS: [[usize; 3]; 6] = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
    fn renamed(t: Term, to: &[usize; 3]) -> Term {
        match *t.node() {
            Node::V(i) => Term::v(to[i]),
            Node::Op(o, a, b) => Term::op(o, renamed(a, to), renamed(b, to)),
            _ => t,
        }
    }
    let mut best: Option<String> = None;
    for p in &PERMS {
        for (l, r) in [(a, b), (b, a)] {
            let s = format!("{} = {}", side(renamed(*l, p)).show(), side(renamed(*r, p)).show());
            if best.as_ref().is_none_or(|k| s < *k) {
                best = Some(s);
            }
        }
    }
    best
}

/// The twin key is the same for two laws that differ by renaming variables, is `None` for a law whose sides are equal
/// below their roots, keeps each side's root (both sides of `sub(y, y) = and(x, 0)` are `0`), and leaves a law between
/// two members of one class (associativity) nontrivial.
#[test]
pub fn twin_keys_rename_normalize_below_roots_and_keep_them() {
    let p = parse_term;
    let swap = twin_key(&p("sub(or(y, x), y)"), &p("and(y, z)"));
    assert_eq!(twin_key(&p("sub(or(x, y), x)"), &p("and(x, z)")), swap, "renaming x and y");
    assert!(swap.is_some());
    assert_eq!(twin_key(&p("add(sub(y, y), x)"), &p("add(0, x)")), None, "sides equal below their roots");
    assert!(twin_key(&p("sub(y, y)"), &p("and(x, 0)")).is_some(), "a side's root stays");
    assert!(twin_key(&p("add(add(x, y), z)"), &p("add(x, add(y, z))")).is_some(), "a law within one class");
    assert_eq!(twin_key(&p("and(or(x, sub(y, 0)), z)"), &p("z")), twin_key(&p("and(or(x, y), z)"), &p("z")), "padding below the root");
}

/// `x`, `y`, `z`, `0` and `-1`.
fn leaves3() -> Vec<Term> {
    (0..3).map(Term::v).chain([Term::ZERO, Term::ONES]).collect()
}

fn mk(o: usize, a: &Term, b: &Term) -> Term {
    Term::op(o, *a, *b)
}

#[test]
pub fn tie_break_orients_reassociation_and_leaves_commutativity_permutative() {
    let t = |s: &str| parse_term(s);
    for (l, r) in [("sub(sub(x, y), z)", "sub(x, add(y, z))"), ("add(sub(x, y), z)", "sub(add(x, z), y)")] {
        let (l, r) = (t(l), t(r));
        assert!(!rule_order_ok(&l, &r) && rule_order_or_tie(&l, &r), "{} -> {}", l.show(), r.show());
        assert!(!rule_order_or_tie(&r, &l), "{} -> {} must not be oriented both ways", r.show(), l.show());
    }
    let (l, r) = (t("add(x, y)"), t("add(y, x)"));
    // commutativity is not oriented by the tie-break; it is permutative (instance-ordered), in both directions
    assert!(!tie_greater(&l, &r) && !tie_greater(&r, &l) && rule_permutative(&l, &r) && rule_permutative(&r, &l));
}

#[test]
pub fn permutative_rules_are_admitted_and_oriented_by_instance() {
    let t = |s: &str| parse_term(s);
    let (l, r) = (t("add(sub(x, y), z)"), t("add(sub(z, y), x)"));
    assert!(rule_permutative(&l, &r) && rule_order_or_tie(&l, &r));
    assert!(!rule_permutative(&t("sub(sub(x, y), z)"), &t("sub(x, add(y, z))")), "reassociation is oriented by the tie-break instead");
}

/// Debug aid: the normal forms of both sides of the laws in `NF_LAWS` (`lhs = rhs` per line) under the built-in rules plus
/// the `lhs -> rhs` rules in `NF_RULES`, three variables, width 4.
#[test]
#[ignore]
pub fn normal_forms() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let rules: Vec<(Term, Term)> = parse_rules(&std::fs::read_to_string(job.setup().var("NF_RULES").unwrap_or_default()).unwrap_or_default());
        let rules = job.rules().with_mined(job.setup(), rules).tracing(job.setup().flag("NF_TRACE", false));
        job.with_rules(rules, |job| {
            let (n, k) = (4, 3);
            for line in std::fs::read_to_string(job.setup().var("NF_LAWS").unwrap()).unwrap().lines().filter(|l| l.contains(" = ")) {
                let (a, b) = line.split_once(" = ").unwrap();
                let (a, b) = (parse_term(a), parse_term(b));
                // each side with its own budget, as in `rewrite_law`; `steps` is what each used (200 or more: it used the budget up)
                let mut side = |t: &Term| {
                    let (nf, spent) = job.measured(LAW_STEPS, |job| rewrite(job, t, n, k).0);
                    (nf, spent.steps)
                };
                let ((na, sa), (nb, sb)) = (side(&a), side(&b));
                let carries = |t: &Term| Machine::parse(t).map_or(0, |m| m.carries());
                println!("NF {} | {} {} carries {}/{} steps {sa}/{sb}", na.show(), nb.show(), if na == nb { "SAME" } else { "DIFF" }, carries(&na), carries(&nb));
            }
        })
    })
}

/// The `shrnot` rule and the laws it closes: a shift of a bitwise not distributes over xor, so both sides reach the same
/// xor of shifted atoms without a whole-term machine proof.
#[test]
pub fn shrnot_rule_is_provable_and_closes_the_shr_not_laws() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        for n in [4usize, 8] {
            let (l, r) = shrnot_rule();
            let (p, s) = prove_rule(job, n, 1, &l, &r).expect("shrnot");
            job.lemmas.ck(&format!("shrnot n={n}"), &p, &s);
        }
        for (a, b) in [
            ("shr1(sub(-1, xor(x, y)), 0)", "xor(shr1(y, 0), xor(shr1(-1, 0), shr1(x, 0)))"),
            ("shr1(xor(xor(x, y), -1), 0)", "shr1(xor(sub(-1, x), y), 0)"),
        ] {
            let (proof, spent) = job.spent(|job| rewrite_law(job, 4, 2, &parse_term(a), &parse_term(b)));
            let (p, s) = proof.unwrap_or_else(|| panic!("{a} = {b}"));
            job.lemmas.ck(a, &p, &s);
            assert_eq!(spent.fallbacks, 0, "{a} = {b} needed a machine proof");
        }
    })
}

/// The setup of the rule-set check tests: the `CHECK_RULES` (none when unset, printed as `CHECK_RULES none`) as the job's
/// rules to install, in file order, the stream laws' variable count, and the `lhs = rhs` laws of `CHECK_LAWFILE` (required,
/// as the driver passes them) that are plausible at widths 1-6.
fn check_laws(job: &Job) -> (Rules, Vec<(Term, Term)>, usize, Vec<(String, Term, Term)>) {
    let text = match job.setup().var("CHECK_RULES") {
        Some(f) => std::fs::read_to_string(f).unwrap(),
        None => {
            println!("CHECK_RULES none");
            String::new()
        }
    };
    let rules = parse_rules(&text);
    let kv = STREAM_VARS;
    let laws = read_named_laws(job.setup().var("CHECK_LAWFILE").expect("CHECK_LAWFILE: the laws to check"));
    let laws = laws.into_iter().filter(|(_, t1, t2)| t1.is_law(t2, kv)).collect();
    let installed = job.rules().with_mined(job.setup(), rules.clone());
    (installed, rules, kv, laws)
}

/// Kernel check of a rule set (search note section 75): every law of `CHECK_LAWFILE`
/// that `rewrite_law` proves under the built-in rules (less `ABLATE`) plus the rules in `CHECK_RULES` is
/// checked by the kernel at width 4; prints how many were proved, how many without a whole-term machine proof, and per law
/// `MACHINE <count> <law>` for the others and `EXHAUSTED <law>` for one that used up the step budget.
#[test]
#[ignore]
pub fn rule_set_kernel_check() {
    rule_set_kernel_check_task(&Setup::process())
}

pub fn rule_set_kernel_check_task(setup: &Arc<Setup>) {
    let job = &mut Job::new(setup.clone());
    let _save = lemma_cache::Save(setup.clone());
    tatic::kernel::scoped(|| {
        let (rules, _, kv, laws) = check_laws(job);
        // CHECK_FAST=1: count only (machine fallbacks are counted without building their proofs, nothing is kernel-checked, no NFSAME pass);
        // the CHECKED line and so M are unchanged, for exploration (the miner's RULEMINER_FAST, applied to serving)
        let fast = job.setup().flag("CHECK_FAST", false);
        job.with_rules(rules.counting(fast), |job| {
            let (mut proved, mut free, mut none, mut exhausted, mut joined) = (0, 0, 0, 0, 0);
            let mut cost = JoinCost::default();
            for (name, t1, t2) in &laws {
                // the proof is built under what the plan left of the budget, and its machine proofs and joins count too
                let ((r, plan_spent, proof), spent) = job.measured(LAW_STEPS, |job| {
                    let (r, plan_spent) = job.spent(|job| job.steps_if_closed(|job| rewrite_plan(job, 4, kv, t1, t2)));
                    let proof = r.as_ref().filter(|_| !fast).map(|plan| law_proof(job, 4, kv, t1, t2, plan));
                    (r, plan_spent, proof)
                });
                cost.add(spent.join);
                // a law that used up the step budget: a rewrite cycle, or rules that grow (docs/tier-cycle.md, "A rewrite cycle")
                if plan_spent.steps >= LAW_STEPS {
                    exhausted += 1;
                    println!("EXHAUSTED {name}");
                }
                if let Some((p, s)) = proof {
                    job.lemmas.ck(name, &p, &s);
                }
                match r {
                    Some(_) => {
                        proved += 1;
                        let machine = spent.fallbacks;
                        free += (machine == 0) as u32;
                        joined += (machine == 0 && spent.join.met > 0) as u32;
                        if machine > 0 {
                            println!("MACHINE {machine} {name}");
                        }
                    }
                    None => none += 1,
                }
            }
            println!("CHECKED {proved} laws kernel-checked ({free} with no whole-term machine proof), {none} not proved, {exhausted} used up the rule budget");
            println!("JOINED {joined} of them by the join, {} searches reaching {} terms", cost.searches, cost.reached);
            for (key, v) in [("proved", proved), ("free", free), ("none", none), ("exhausted", exhausted), ("joined", joined)].map(|(k, v)| (k, u64::from(v))).into_iter().chain([("reached", cost.reached), ("classes", job.table_steps.len() as u64)]) {
                job.setup().result(key, v);
            }
            if fast {
                return;
            }
            // confluence on this law set: both sides of a law reach the same normal form (the check above counts machine-free proofs, which can also come from a middle term)
            let (mut same, mut total) = (0, 0);
            for (_, t1, t2) in &laws {
                let n1 = job.measured(LAW_STEPS, |job| rewrite(job, t1, 4, kv).0).0;
                let n2 = job.measured(LAW_STEPS, |job| rewrite(job, t2, 4, kv).0).0;
                total += 1;
                same += (n1 == n2) as u32;
            }
            println!("NFSAME {same} of {total} laws have equal normal forms on both sides");
        })
    });
}

/// Where the kernel's work goes under a rule set: like `rule_set_kernel_check` (same `CHECK_RULES` and `CHECK_LAWFILE`), but
/// reports, for the laws proved by rules alone ("rules"), by rules and the join with no whole-term machine proof ("joined"), and
/// for those that needed one ("machine"), the count, the
/// time to build the proof, the time for the kernel to check it, and its size (unique nodes / nodes per occurrence); then the same
/// for the proofs of the rules themselves, which a conversion rule or a one-time admission would pay once.
#[test]
#[ignore]
pub fn proof_cost_split() {
    let job = &mut Job::new(Setup::process());
    use std::time::{Duration, Instant};
    tatic::kernel::scoped(|| {
        let (installed, rules, kv, laws) = check_laws(job);
        job.with_rules(installed, |job| {
            #[derive(Default)]
            struct Acc { n: u32, build: Duration, check: Duration, nodes: usize, occ: u128 }
            let mut acc = [Acc::default(), Acc::default(), Acc::default()]; // [rules, joined, machine]
            let mut none = 0;
            for (name, t1, t2) in &laws {
                let t = Instant::now();
                let (proof, spent) = job.measured(LAW_STEPS, |job| rewrite_law(job, 4, kv, t1, t2));
                let Some((p, s)) = proof else { none += 1; continue };
                let build = t.elapsed();
                let t = Instant::now();
                job.lemmas.ck(name, &p, &s);
                let check = t.elapsed();
                let (nodes, occ) = tatic::kernel::term_sizes(&p);
                let a = &mut acc[if spent.fallbacks != 0 { 2 } else { (spent.join.met > 0) as usize }];
                (a.n, a.build, a.check, a.nodes, a.occ) = (a.n + 1, a.build + build, a.check + check, a.nodes + nodes, a.occ + occ);
            }
            let mut ra = Acc::default();
            for (l, r) in &rules {
                let k = l.max_var().max(r.max_var()) + 1;
                let t = Instant::now();
                let Some((p, ty)) = prove_rule(job, 4, k, l, r) else { continue };
                let build = t.elapsed();
                let t = Instant::now();
                job.lemmas.ck(&l.show(), &p, &ty);
                let check = t.elapsed();
                let (nodes, occ) = tatic::kernel::term_sizes(&p);
                (ra.n, ra.build, ra.check, ra.nodes, ra.occ) = (ra.n + 1, ra.build + build, ra.check + check, ra.nodes + nodes, ra.occ + occ);
            }
            for (what, a) in [("rules", &acc[0]), ("joined", &acc[1]), ("machine", &acc[2]), ("rule-proofs", &ra)] {
                println!("COST {what}: n={} build={:.1}ms check={:.1}ms nodes={} occurrences={}", a.n, a.build.as_secs_f64() * 1e3, a.check.as_secs_f64() * 1e3, a.nodes, a.occ);
            }
            println!("COST not-proved={none}");
        })
    });
}

/// Closed terms equal to 0, -1 or 1 normalize to `0`, `-1`, `sub(0, -1)` with no machine proof (by the rules and the class table; a
/// constant-folding step of its own was removed as redundant).
#[test]
pub fn closed_terms_fold_to_constants() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        for (a, b) in [("sub(-1, add(-1, -1))", "sub(0, -1)"), ("sub(add(0, 0), -1)", "sub(0, -1)"), ("xor(-1, -1)", "0"), ("add(-1, add(-1, sub(0, -1)))", "-1")] {
            let (t1, t2) = (parse_term(a), parse_term(b));
            let (proof, spent) = job.spent(|job| rewrite_law(job, 4, 1, &t1, &t2));
            let (p, ty) = proof.unwrap_or_else(|| panic!("{a} = {b} not proved"));
            job.lemmas.ck(a, &p, &ty);
            assert_eq!(spent.fallbacks, 0, "{a} = {b} needed a machine proof");
        }
    })
}

// --- Proposal yield (docs/tier-cycle.md): what a proposer's samples are worth to the kernel ---

/// The kernel's cost for a true law under the installed rules: whole-term machine proofs and rule steps (of a `LAW_STEPS` budget) that
/// `rewrite_law` used, and whether it proved the law at all. The difficulty grade a proposer is scored by.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Cost {
    pub fallbacks: u64,
    pub steps: i64,
    pub proved: bool,
}

impl Cost {
    /// The band the miner learns from: laws that still need a machine proof (the ones M counts), or were not proved.
    pub fn hard(&self) -> bool {
        !self.proved || self.fallbacks > 0
    }
}

/// The `Cost` of `t1 = t2` under the job's rules (a `LAW_STEPS` budget, width 4).
pub fn law_cost(job: &mut Job, kv: usize, t1: &Term, t2: &Term) -> Cost {
    let (proved, spent) = job.measured(LAW_STEPS, |job| rewrite_plan(job, 4, kv, t1, t2).is_some());
    Cost { fallbacks: spent.fallbacks, steps: spent.steps, proved }
}

/// Per-proposal credit for a mined library `rules` (docs/tier-cycle.md). Each rule's held-out gain is how many more `held` laws are hard
/// without it; a proposal uses a rule when it is cheap under `rules` but hard without that rule; each rule's gain is split evenly over
/// the proposals that use it. Returns the per-rule gains, the per-rule user counts and the per-proposal credits.
pub fn proposal_credit(job: &mut Job, rules: &[(Term, Term)], kv: usize, held: &[(Term, Term)], props: &[(Term, Term)]) -> (Vec<i64>, Vec<usize>, Vec<f64>) {
    let hard = |job: &mut Job, set: &[(Term, Term)], laws: &[(Term, Term)]| -> Vec<bool> {
        job.with_mined(set.to_vec(), |job| laws.iter().map(|(a, b)| law_cost(job, kv, a, b).hard()).collect())
    };
    let count = |v: &[bool]| v.iter().filter(|h| **h).count() as i64;
    let (held_all, props_all) = (count(&hard(job, rules, held)), hard(job, rules, props));
    let (mut gains, mut users, mut credit) = (vec![], vec![], vec![0.0; props.len()]);
    for i in 0..rules.len() {
        let without: Vec<(Term, Term)> = rules.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, r)| *r).collect();
        let gain = count(&hard(job, &without, held)) - held_all;
        let uses: Vec<usize> = hard(job, &without, props).iter().zip(&props_all).enumerate().filter(|(_, (h, h_all))| **h && !**h_all).map(|(p, _)| p).collect();
        for &p in &uses {
            credit[p] += gain as f64 / uses.len() as f64;
        }
        gains.push(gain);
        users.push(uses.len());
    }
    (gains, users, credit)
}

/// Credit for the proposals in `CREDIT_LAWS` (`lhs = rhs` lines) from the library `CHECK_RULES` mined on them, against the held-out
/// laws of `CHECK_LAWFILE`. Prints a `CREDIT rule` line per rule (held-out gain,
/// users) and a `CREDIT total` line; `CREDIT_OUT` saves `credit<TAB>law` per proposal.
#[test]
#[ignore]
pub fn proposal_credit_report() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let (installed, rules, kv, laws) = check_laws(job);
        job.with_rules(installed.counting(true), |job| {
            let held: Vec<(Term, Term)> = laws.into_iter().map(|(_, a, b)| (a, b)).collect();
            let props = read_laws(&job.setup().var("CREDIT_LAWS").unwrap());
            let (gains, users, credit) = proposal_credit(job, &rules, kv, &held, &props);
            for (i, (l, r)) in rules.iter().enumerate() {
                println!("CREDIT rule {} -> {}: held-out gain {}, used by {} proposals", l.show(), r.show(), gains[i], users[i]);
            }
            let m0 = job.with_mined(vec![], |job| held.iter().filter(|(a, b)| law_cost(job, kv, a, b).hard()).count());
            let m1 = held.iter().filter(|(a, b)| law_cost(job, kv, a, b).hard()).count();
            let credited = credit.iter().filter(|c| **c != 0.0).count();
            println!(
                "CREDIT total: held-out M {m0} -> {m1} (gain {}), sum of rule gains {}, attributed {:.1}, {credited} of {} proposals credited",
                m0 as i64 - m1 as i64,
                gains.iter().sum::<i64>(),
                credit.iter().sum::<f64>(),
                props.len()
            );
            if let Some(out) = job.setup().var("CREDIT_OUT") {
                let text: String = props.iter().zip(&credit).map(|((a, b), c)| format!("{c:.3}\t{} = {}\n", a.show(), b.show())).collect();
                std::fs::write(out, text).unwrap();
            }
        })
    })
}

/// A rule's credit goes to the proposal that needs it, in proportion to its held-out gain.
#[test]
pub fn proposal_credit_goes_to_rule_users() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let counting = job.rules().counting(true);
        job.with_rules(counting, |job| {
            let law = |s: &str| s.split_once(" = ").map(|(a, b)| (parse_term(a), parse_term(b))).unwrap();
            let rules = parse_rules("lt(x, sub(x, y)) -> lt(x, y)\n");
            // the proposal and the held-out law are both closed by the rule only if the built-in rules do not already close them
            let (p, h) = (law("lt(x, sub(x, y)) = lt(x, y)"), law("lt(z, sub(z, x)) = lt(z, x)"));
            let (gains, users, credit) = proposal_credit(job, &rules, 3, &[h], &[p, law("add(x, y) = add(y, x)")]);
            assert_eq!(gains.len(), 1);
            assert_eq!(credit[1], 0.0, "a proposal that does not use the rule gets nothing");
            assert_eq!(credit[0], if users[0] == 1 { gains[0] as f64 } else { 0.0 });
        })
    })
}

/// The `lhs = rhs` lines of a file as term pairs.
pub fn read_laws(path: &str) -> Vec<(Term, Term)> {
    std::fs::read_to_string(path).unwrap().lines().filter_map(|l| l.split_once(" = ")).map(|(a, b)| (parse_term(a), parse_term(b))).collect()
}

/// `read_laws` with each law named by its `lhs = rhs` text.
pub fn read_named_laws(path: &str) -> Vec<(String, Term, Term)> {
    read_laws(path).into_iter().map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b)).collect()
}
