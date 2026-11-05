use super::*;

/// `Term::op` makes one node per term whatever a thread's cache holds: terms made on another thread are the same pointers,
/// and each node is the one asked for, with more terms than cache slots so that slots are shared.
#[test]
fn op_is_one_node_per_term_across_threads() {
    let build = || {
        let mut level = vec![Term::v(0), Term::v(1), Term::ZERO, Term::ONES];
        let mut out = vec![];
        for _ in 0..3 {
            let mut next = vec![];
            for o in 0..5 {
                for &a in &level {
                    for &b in level.iter().take(100_000 / (5 * level.len()) + 1) {
                        next.push(((o, a, b), Term::op(o, a, b)));
                    }
                }
            }
            level = next.iter().map(|e| e.1).collect();
            out.extend(next);
        }
        out
    };
    let (here, there, again) = (build(), std::thread::spawn(build).join().unwrap(), build());
    assert!(here.len() > 1 << 16, "more terms than cache slots");
    for (((o, a, b), t), (_, u)) in here.iter().zip(&there) {
        assert!(*t.node() == Node::Op(*o, *a, *b), "the node asked for");
        assert!(t == u, "one node across threads");
    }
    assert!(here.iter().zip(&again).all(|(x, y)| x.1 == y.1), "one node on a second look");
}

/// Threads making the same new terms at once (racing to insert them, and the table growing under them) get one node each.
#[test]
fn op_racing_threads_make_one_node_per_term() {
    let barrier = std::sync::Barrier::new(8);
    let build = || {
        barrier.wait();
        // terms no other test makes: variable 40 on the left of every one
        let mut level = vec![Term::v(40), Term::v(41), Term::v(42)];
        let mut out = vec![];
        for _ in 0..3 {
            let next: Vec<Term> = (0..5).flat_map(|o| level.iter().flat_map(move |&a| [Term::v(40), Term::v(43)].map(|b| (o, a, b)))).map(|(o, a, b)| Term::op(o, a, b)).collect();
            out.extend(&next);
            level = next;
        }
        let wide: Vec<Term> = out.iter().flat_map(|&a| out.iter().take(200).map(move |&b| Term::op(4, a, b))).collect();
        out.extend(wide);
        out
    };
    let all: Vec<Vec<Term>> = std::thread::scope(|s| (0..8).map(|_| s.spawn(build)).collect::<Vec<_>>().into_iter().map(|h| h.join().unwrap()).collect());
    assert!(all[0].len() > 100_000, "enough new terms to grow the table");
    assert!(all.iter().all(|v| v == &all[0]), "one node per term across racing threads");
}

#[test]
pub fn bitwise_law_proves_true_laws_and_rejects_false_ones() {
    let v = |i: usize| Term::v(i);
    let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("and x y = and y x", op(1, v(0), v(1)), op(1, v(1), v(0))),
            ("xor x x = 0", op(3, v(0), v(0)), Term::ZERO),
            ("or x -1 = -1", op(2, v(0), Term::ONES), Term::ONES),
            ("and x (or x y) = x", op(1, v(0), op(2, v(0), v(1))), v(0)),
        ] {
            let (p, s) = bitwise_law(n, &t1, &t2);
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        for (name, t1, t2) in [("and x y = or x y", op(1, v(0), v(1)), op(2, v(0), v(1))), ("xor x x = -1", op(3, v(0), v(0)), Term::ONES)] {
            let (p, s) = bitwise_law(n, &t1, &t2);
            assert!(holds(&p, &s).is_err(), "false law `{name}` must be rejected at n={n}");
        }
    }
}

#[test]
fn rule_order_does_not_change_rewriting() {
    let job = &Job::new(Setup::process());
    // overlapping rules: under list order the first one would win on sub(sub(x, y), z) whichever it is
    let a = "sub(sub(x, y), z) -> sub(x, add(y, z))\nsub(x, y) -> add(x, sub(0, y))\nsub(sub(x, y), z) -> sub(sub(x, z), y)\n";
    let b = "sub(sub(x, y), z) -> sub(sub(x, z), y)\nsub(x, y) -> add(x, sub(0, y))\nsub(sub(x, y), z) -> sub(x, add(y, z))\n";
    let installed = |text: &str| -> Vec<String> { Rules::new(job.setup(), parse_rules(text)).mined().iter().map(|(l, r)| format!("{} -> {}", l.show(), r.show())).collect() };
    let (ia, ib) = (installed(a), installed(b));
    assert_eq!(ia, ib);
    assert!(ia.last().unwrap().starts_with("sub(x, y)"), "the general rule goes after the specific ones: {ia:?}");
}

/// A rule no other route proves, with `shr1` under `add` (a carry machine refuses `shr1`), is proved over every input
/// when it has at most `EVERY_INPUT_BITS` input bits; a false one is not, nor a true one past the cap (docs/tier-cycle.md,
/// "At the loops' width, every-input proofs").
#[test]
fn a_rule_past_every_route_is_proved_over_every_input() {
    let job = &mut Job::new(Setup::process());
    let rule = |l: &str, r: &str| (parse_term(l), parse_term(r));
    let k = |(l, r): &(Term, Term)| l.max_var().max(r.max_var()) + 1;
    let shr = rule("add(and(add(x, shr1(-1, 0)), shr1(y, 0)), z)", "add(z, and(add(x, -1), shr1(y, 0)))");
    assert!(prove_rule(job, 4, k(&shr), &shr.0, &shr.1).is_some());
    let lt = rule("lt(shr1(x, 0), x)", "lt(0, x)");
    assert!(prove_rule(job, 4, k(&lt), &lt.0, &lt.1).is_some());
    let wrong = rule("add(and(add(x, shr1(-1, 0)), shr1(y, 0)), z)", "add(z, and(add(x, -1), shr1(z, 0)))");
    assert!(prove_rule(job, 4, k(&wrong), &wrong.0, &wrong.1).is_none());
    let wide = rule("add(and(add(x, shr1(-1, 0)), shr1(y, 0)), add(z, u))", "add(add(z, u), and(add(x, -1), shr1(y, 0)))");
    assert!(prove_rule(job, 4, k(&wide), &wide.0, &wide.1).is_none(), "16 input bits is past the cap");
}

/// A proof neither sees nor changes the caller's `rewrote` (Q4): before, it took the list over, so the terms the proof
/// took up joined it, or the proof's last rewrite cleared it.
#[test]
fn a_proof_leaves_the_callers_rewrote_alone() {
    let job = &mut Job::new(Setup::process());
    let t = parse_term("add(x, y)");
    job.rw.rewrote.push(t);
    let seen = proving(job, &[], |job| job.rw.rewrote.len());
    assert_eq!(seen, 0, "the proof starts with a list of its own");
    assert!(job.rw.rewrote.len() == 1 && job.rw.rewrote[0] == t, "the caller's list is as it was");
}

#[test]
fn unification_and_overlaps() {
    let t = parse_term;
    assert!(unify(&t("sub(sub(x, y), z)"), &t("sub(u, add(x, y))"), &mut vec![None; 8]));
    assert!(!unify(&t("x"), &t("add(x, y)"), &mut vec![None; 8]), "occurs check");
    assert!(!unify(&t("sub(x, x)"), &t("sub(0, -1)"), &mut vec![None; 8]), "a variable takes one value");
    // the two sub/sub orientations overlap at the root; sub(x, y) -> .. overlaps both below and at the root
    let rules = parse_rules("sub(sub(x, y), z) -> sub(x, add(y, z))\nsub(sub(x, y), z) -> sub(sub(x, z), y)\nlt(x, add(y, z)) -> lt(x, add(z, y))\n");
    let o = rule_overlaps(&rules);
    assert!(o.contains(&(0, 1, true)) && o.contains(&(1, 0, true)));
    assert!(o.contains(&(0, 0, false)), "sub(sub(x, y), z) also matches its own inner sub(x, y) position");
    assert!(!o.iter().any(|&(i, j, _)| (i == 2) != (j == 2)), "lt rules do not overlap sub rules: {o:?}");
}

/// `OVERLAP_RULES=<rules file>`: prints every overlapping pair of the file's rules and the counts.
#[test]
#[ignore]
fn rule_overlap_report() {
    let job = &Job::new(Setup::process());
    let rules = parse_rules(&std::fs::read_to_string(job.setup().var("OVERLAP_RULES").expect("set OVERLAP_RULES=<file>")).unwrap());
    let o = rule_overlaps(&rules);
    // a root overlap where one left side is an instance of the other is settled by specific-first order; the rest are not
    let inst = |a: &Term, b: &Term| match_pat(a, b, &mut vec![None; a.max_var() + 1]);
    let mut kinds = [0usize; 3];
    for &(i, j, root) in &o {
        let (li, lj) = (&rules[i].0, &rules[j].0);
        let kind = if !root { 0 } else if inst(li, lj) || inst(lj, li) { 1 } else { 2 };
        kinds[kind] += 1;
        println!("OVERLAP {} {} -> {}  WITH  {} -> {}", ["inner", "nested", "cross"][kind], li.show(), rules[i].1.show(), lj.show(), rules[j].1.show());
    }
    let touched: hashbrown::HashSet<usize> = o.iter().flat_map(|&(i, j, _)| [i, j]).collect();
    println!(
        "OVERLAPS {} rules, {} overlapping pairs: {} inner, {} at the root with one left side an instance of the other, {} at the root otherwise; {} rules in some overlap",
        rules.len(), o.len(), kinds[0], kinds[1], kinds[2], touched.len()
    );
}

/// `embeds` on chains of one operator: `s` is y under 50 `add(_, x)` nodes and `t` is z under 60, so `s` does not embed,
/// and the plain recursion, coupling or skipping at each of `t`'s 60 nodes, makes about 3 x 2^60 = 3.5e18 calls. A
/// sweep's mine spun on such a pair for hours (docs/tier-cycle.md, "The hang"). With y at the bottom of both, `s` embeds
/// (the plain recursion finds it in 111 calls: this half checks the answer, not the speed).
#[test]
fn embedding_long_chains_finishes() {
    let chain = |leaf, n| (0..n).fold(Term::v(leaf), |c, _| Term::op(ADD, c, Term::v(0)));
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let s = chain(1, 50);
        let _ = tx.send((embeds(&s, &chain(2, 60)), embeds(&s, &chain(1, 60))));
    });
    assert_eq!(rx.recv_timeout(std::time::Duration::from_secs(10)), Ok((false, true)), "an answer within 10 s");
}

/// `embeds` gives the plain recursion's answer (Kruskal's definition, kept here as the reference) on every pair of terms over
/// `add`, `and`, x, y, 0 and -1: those of up to 5 nodes against those of up to 7.
#[test]
fn embedding_matches_the_plain_recursion() {
    fn plain(s: &Term, t: &Term) -> bool {
        let couple = match (*s.node(), *t.node()) {
            (Node::V(i), Node::V(j)) => i == j,
            (Node::Zero, Node::Zero) | (Node::Ones, Node::Ones) => true,
            (Node::Op(f, s1, s2), Node::Op(g, t1, t2)) => f == g && plain(&s1, &t1) && plain(&s2, &t2),
            _ => false,
        };
        couple || matches!(*t.node(), Node::Op(_, t1, t2) if plain(s, &t1) || plain(s, &t2))
    }
    // the terms by size: sized[n] holds those of n nodes
    let mut sized: Vec<Vec<Term>> = vec![vec![], vec![Term::v(0), Term::v(1), Term::ZERO, Term::ONES]];
    for n in 2..=7 {
        let mut ts = vec![];
        for a in 1..n - 1 {
            for x in &sized[a] {
                for y in &sized[n - 1 - a] {
                    ts.extend([ADD, AND].map(|o| Term::op(o, *x, *y)));
                }
            }
        }
        sized.push(ts);
    }
    let (small, all) = (sized[..=5].concat(), sized.concat());
    let (mut pairs, mut yes, mut differ) = (0, 0, vec![]);
    for s in &small {
        for t in &all {
            let e = embeds(s, t);
            if e != plain(s, t) {
                differ.push(format!("{} in {}: {e}", s.show(), t.show()));
            }
            (pairs, yes) = (pairs + 1, yes + e as usize);
        }
    }
    println!("{pairs} pairs, {yes} embed");
    assert!(differ.is_empty(), "{} of {pairs} differ, first: {:?}", differ.len(), &differ[..differ.len().min(5)]);
    assert!(yes > 0 && yes < pairs, "both answers occur");
}

/// After a step, `join_walk` skips the subtrees left of the step's path: there a step and this one, the other
/// taken first, would reach the same term. Its ancestors, the rewritten subterm and what is right of it stay.
#[test]
fn join_walk_after_a_step_skips_the_subtrees_left_of_its_path() {
    // the step rewrote `c` in `add(and(a, b), or(c, d))`: right at the root, then left
    let t = parse_term("add(and(x, y), or(xor(x, y), sub(y, x)))");
    let table = RuleTable::new(&Setup::process(), vec![]);
    let walked = |order: Option<StepPath>| {
        let mut examined = Some(hashbrown::HashSet::default());
        join_walk(t, order, &table, &[], 1000, &mut vec![], &mut examined, &mut |_, _, _, _, _| true);
        let mut v: Vec<String> = examined.unwrap().into_iter().map(|t| t.show()).collect();
        v.sort();
        v
    };
    let mut all = vec![];
    t.subterms(&mut all);
    let mut want: Vec<String> = all.iter().map(|t| t.show()).collect::<std::collections::BTreeSet<_>>().into_iter().collect();
    assert_eq!(walked(None), want);
    // `and(x, y)` is left of the path; `x` and `y` stay, as subterms of the right side too
    want.retain(|s| s != "and(x, y)");
    assert_eq!(walked(Some(StepPath { at: 5 })), want);
    // a step at the root leaves nothing to its left
    assert_eq!(walked(Some(StepPath { at: 0 })).len(), want.len() + 1);
}

/// A step orders the walk after it only when it did not shrink the term: then the other order's middle term is no larger
/// than the end term, so within the cap whenever the end term is.
#[test]
fn a_join_step_orders_the_walk_after_it_only_when_it_did_not_shrink_the_term() {
    let (from, path) = (parse_term("add(and(x, y), add(z, 0))"), StepPath { at: 4 });
    let step = JoinStep { from, path, eq: 0 };
    let ordered = |to: &str| step.order(parse_term(to)).map(|p| p.at);
    assert_eq!(ordered("add(and(x, y), z)"), None, "the step shrank the term");
    assert_eq!(ordered("add(and(x, y), add(0, z))"), Some(4), "same size");
    assert_eq!(ordered("add(and(x, y), add(z, add(0, 0)))"), Some(4), "grew");
}

/// A join step's path holds at any depth: band-17 mines reached depth 69 in a 1423-node term, where a 64-bit path lost
/// its top levels and `Spine::down` walked off a leaf (run `2026-10-25-held-seen`).
#[test]
fn a_join_steps_path_holds_past_depth_64() {
    // 70 levels, going left at every third one
    let left = |i: usize| i % 3 == 0;
    let chain = |bottom: Term| (0..70).rev().fold(bottom, |t, i| if left(i) { Term::op(ADD, t, Term::v(0)) } else { Term::op(ADD, Term::v(0), t) });
    let from = chain(Term::v(1));
    let (mut up, mut x) = (vec![], from);
    while let Node::Op(o, a, b) = *x.node() {
        let right = !left(up.len());
        up.push((o, a, b, right));
        x = if right { b } else { a };
    }
    assert!(up.len() == 70 && x == Term::v(1));
    let (step, at) = (JoinStep::new(from, &up, 0), Term::v(2));
    assert!(step.spine(at).make() == chain(at), "the spine rebuilds the reached term");
    assert!(step.spine(at).is(chain(at)), "and recognises it");
}

/// `Need::skips` skips a match only when its step is over the cap, and every match over the cap for a rule that repeats
/// no variable, such as commutativity: so `join_walk` skipping by it changes no search.
#[test]
fn join_need_skips_only_steps_over_the_cap() {
    let job = &Job::new(Setup::process());
    let rule = |l: &str, r: &str| TableRule { name: "t", lhs: parse_term(l), rhs: parse_term(r), vars: 2, permutative: false };
    let eqs = join_eqs(job.setup(), &[rule("and(x, or(x, y))", "x"), rule("add(x, x)", "shl1(x, 0)"), rule("xor(x, y)", "xor(y, xor(x, 0))")]);
    let mut terms = vec![Term::v(0), Term::v(1), Term::ZERO];
    for _ in 0..2 {
        let level: Vec<Term> = terms.iter().flat_map(|&a| terms.iter().flat_map(move |&b| [ADD, AND, OR, XOR, SHL1].map(|o| Term::op(o, a, b)))).collect();
        terms.extend(level);
    }
    let (mut matched, mut exact) = (0, 0);
    for e in &eqs {
        for &t in &terms {
            let mut sub = [None; RULE_VARS];
            if match_pat(&e.from, &t, &mut sub) {
                let size = subst_sig(&e.to, &sub).1;
                let skips: Vec<bool> = (0..size + 3).map(|cap| e.need.skips(cap as isize - t.size() as isize, cap as isize)).collect();
                for (cap, &s) in skips.iter().enumerate() {
                    assert!(!s || size > cap, "{} -> {} at {}: skipped at cap {cap}, step {size}", e.from.show(), e.to.show(), t.show());
                }
                matched += 1;
                exact += (matches!(e.kind, LawKind::Comm) && skips.iter().enumerate().all(|(cap, &s)| s == (size > cap))) as usize;
            }
        }
    }
    assert!(matched > 1000 && exact > 100, "matched {matched}, exact for add's commutativity {exact}");
}


/// One law per kind of step (assoc and comm, a rule, a constant carry, the carry-encoding search, a collapse, an `lt` root, the
/// bit-0 mask): counting (`Rules::counting`) finds it too without building a plan, and the proving plan's sides are the law's and it
/// compiles to a proof the kernel accepts.
#[test]
fn plans_compile_to_checked_proofs() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let (v, z, ones) = (Term::v, Term::ZERO, Term::ONES);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let shr = |a: Term| op(SHR1, a, Term::ZERO);
        let laws = [
            (op(ADD, op(ADD, v(2), v(0)), v(1)), op(ADD, v(1), op(ADD, v(0), v(2)))),
            (op(SHL1, op(AND, v(0), v(1)), z), op(AND, op(SHL1, v(0), z), op(SHL1, v(1), z))),
            (op(ADD, v(0), op(XOR, v(0), ones)), ones),
            (op(SUB, ones, v(1)), op(XOR, v(1), ones)),
            (op(OR, v(0), op(AND, v(0), v(1))), v(0)),
            (op(LT, v(0), op(ADD, v(1), z)), op(LT, v(0), v(1))),
            (shr(op(ADD, v(0), v(0))), shr(op(SUB, op(ADD, v(0), v(0)), ones))),
        ];
        for (l, r) in &laws {
            let k = l.max_var().max(r.max_var()) + 1;
            let plans = [false, true].map(|counting| {
                let rules = job.rules().counting(counting);
                job.with_rules(rules, |job| rewrite_plan(job, 4, k, l, r)).unwrap_or_else(|| panic!("no plan for {} = {} (counting: {counting})", l.show(), r.show()))
            });
            assert!(matches!(*plans[1], Plan::Counting), "counting built a plan for {} = {}", l.show(), r.show());
            let (a, b, _) = Compiler::new(4, k).proof(job, &plans[0]);
            assert!((a, b) == (*l, *r), "{} = {}", l.show(), r.show());
            let (p, s) = law_proof(job, 4, k, l, r, &plans[0]);
            job.lemmas.ck(&format!("{} = {}", l.show(), r.show()), &p, &s);
        }
    })
}

/// The bounded join closes an equal pair by a mined rule and add commutativity (a plan whose sides are the pair's and which
/// the kernel accepts, and which counting finds too), and gives none for a pair that is not equal.
#[test]
fn join_eq_closes_an_equal_pair_by_rule_and_comm_steps() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let rules = job.rules().with_mined(job.setup(), vec![(parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"))]);
        job.with_rules(rules, |job| {
        let (n, k) = (4, 3);
        let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
        let counting = job.rules().counting(true);
        let counted = job.with_rules(counting, |job| join_eq(job, n, k, &a, &b));
        assert!(matches!(counted.as_deref(), Some(Plan::Counting)), "counting found no join");
        let plan = join_eq(job, n, k, &a, &b).expect("a join");
        assert!(Compiler::new(n, k).proof(job, &plan).0 == a && Compiler::new(n, k).proof(job, &plan).1 == b);
        let (p, s) = law_proof(job, n, k, &a, &b, &plan);
        job.lemmas.ck("joined", &p, &s);
        assert!(join_eq(job, n, k, &a, &parse_term("add(sub(add(x, y), -1), y)")).is_none());
        })
    })
}

/// A join step is known before it is made: `subst_sig` and `place_sh` give the `sh` and size of the term `subst_pat` and
/// `Spine::make` make, and `is_step` and `Spine::is_step` know that term from its place and match, against a made term or
/// a step's whose spine is not made, and only it.
#[test]
fn a_join_step_is_known_before_it_is_made() {
    let (x, z) = (Term::v(0), Term::v(2));
    let and = |a, b| Term::op(AND, a, b);
    let or = |a, b| Term::op(OR, a, b);
    let (p, inner) = (parse_term("add(sub(x, y), add(y, -1))"), parse_term("xor(and(z, x), 0)"));
    let mut sub = [None; RULE_VARS];
    (sub[0], sub[1]) = (Some(parse_term("add(y, z)")), Some(inner));
    let u = subst_pat(&p, &sub);
    assert!(subst_sig(&p, &sub) == (u.sh(), u.size()));
    // from `and(or(x, inner), z)`, left then right: `inner` becomes `u`
    let from = and(or(x, inner), z);
    let up = [(AND, or(x, inner), z, false), (OR, x, inner, true)];
    let step = JoinStep::new(from, &up, 0).spine(u);
    let t = step.make();
    assert!(t == and(or(x, u), z) && place_sh(&up, u.sh()) == t.sh());
    assert!(is_step(t, &up, &p, &sub) && step.is(t));
    for (other, why) in [(and(or(x, u), x), "another sibling"), (from, "another replacement"), (and(Term::op(XOR, x, u), z), "another operator")] {
        assert!(!is_step(other, &up, &p, &sub) && !step.is(other), "{why}");
    }
    // the same term by another step, neither spine made: at the same place
    assert!(step.is_step(&up, &p, &sub));
    assert!(!step.is_step(&[(AND, or(x, inner), x, false), (OR, x, inner, true)], &p, &sub), "another sibling");
    // at a place above the spine's end, its pattern down the spine
    let (q, mut sub2) = (parse_term("or(x, y)"), [None; RULE_VARS]);
    (sub2[0], sub2[1]) = (Some(x), Some(u));
    assert!(step.is_step(&[(AND, or(x, x), z, false)], &q, &sub2));
    assert!(!step.is_step(&[(AND, or(x, x), x, false)], &q, &sub2), "another sibling");
    let (r, mut sub3) = (parse_term("and(or(x, y), z)"), [None; RULE_VARS]);
    (sub3[0], sub3[1], sub3[2]) = (Some(x), Some(u), Some(z));
    assert!(step.is_step(&[], &r, &sub3));
    sub3[2] = Some(x);
    assert!(!step.is_step(&[], &r, &sub3), "another sibling under the pattern");
    // a pattern variable above the spine's end
    let (v, mut sub4) = (parse_term("and(y, z)"), [None; RULE_VARS]);
    (sub4[1], sub4[2]) = (Some(or(x, u)), Some(z));
    assert!(step.is_step(&[], &v, &sub4));
    sub4[1] = Some(or(x, inner));
    assert!(!step.is_step(&[], &v, &sub4), "another term for the variable");
    // at a place below the spine's end
    let mut other = sub;
    other[1] = Some(x);
    let shallow = JoinStep::new(from, &up[..1], 0).spine(or(x, u));
    assert!(shallow.make() == t && shallow.is(t) && shallow.is_step(&up, &p, &sub));
    assert!(!shallow.is_step(&up, &p, &other), "another match");
    // a pattern past the spine's end, and another operator under it
    sub3[2] = Some(z);
    assert!(shallow.is_step(&[], &r, &sub3) && !shallow.is_step(&[], &parse_term("and(xor(x, y), z)"), &sub3));
    sub3[1] = Some(x);
    assert!(!shallow.is_step(&[], &r, &sub3), "another term past the spine's end");
    // `and(u, or(x, u))` by a spine down the right child and a step down the left
    let right = JoinStep::new(and(u, z), &[(AND, u, z, true)], 0).spine(or(x, u));
    assert!(right.make() == and(u, or(x, u)) && right.is_step(&[(AND, z, or(x, u), false)], &p, &sub));
    assert!(!right.is_step(&[(AND, z, or(x, x), false)], &p, &sub), "paths apart, another sibling");
    assert!(!right.is_step(&[(AND, z, or(x, u), false)], &p, &other), "paths apart, another match");
    // a pattern at the root down a spine that goes right, and another operator at the root
    let (w, mut sub5) = (parse_term("and(x, y)"), [None; RULE_VARS]);
    (sub5[0], sub5[1]) = (Some(u), Some(or(x, u)));
    assert!(right.is_step(&[], &w, &sub5) && !right.is_step(&[], &parse_term("xor(x, y)"), &sub5));
    sub5[0] = Some(z);
    assert!(!right.is_step(&[], &w, &sub5), "another term off the right");
    (sub5[0], sub5[1]) = (Some(u), Some(or(x, x)));
    assert!(!right.is_step(&[], &w, &sub5), "another term down the right");
}

#[test]
pub fn laws_over_three_vectors_check_and_false_ones_fail() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        for n in [1usize, 3] {
            // bitwise (x ^ y) ^ z = x ^ (y ^ z)
            let (p, s) = bitwise_law_k(n, 3, &op(3, op(3, v(0), v(1)), v(2)), &op(3, v(0), op(3, v(1), v(2))));
            job.lemmas.ck(&format!("xor assoc at n={n}"), &p, &s);
            assert!(job.lemmas.holds(&bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).0, &bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).1).is_err());
            // add associativity over three vectors, and a non-law
            let (p, s) = rewrite_law(job, n, 3, &op(0, op(0, v(0), v(1)), v(2)), &op(0, v(0), op(0, v(1), v(2)))).expect("assoc");
            job.lemmas.ck(&format!("add assoc at n={n}"), &p, &s);
            let (p, s) = rewrite_law(job, n, 3, &op(0, op(0, v(2), v(0)), v(1)), &op(0, v(1), op(0, v(0), v(2)))).expect("comm+assoc");
            job.lemmas.ck(&format!("add comm assoc at n={n}"), &p, &s);
            assert!(rewrite_law(job, n, 3, &op(0, v(0), v(2)), &op(0, v(0), v(1))).is_none());
        }
    })
}

#[test]
pub fn rewrite_law_proves_add_conjectures_from_the_library_lemmas() {
    let job = &mut Job::new(Setup::process());
    let v = |i: usize| Term::v(i);
    let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
    let n = 4;
    for (name, t1, t2) in [
        ("or (add x 0) y = or y x", op(2, op(0, v(0), Term::ZERO), v(1)), op(2, v(1), v(0))),
        ("xor (add x y) y = xor y (add y x)", op(3, op(0, v(0), v(1)), v(1)), op(3, v(1), op(0, v(1), v(0)))),
        ("add (and x y) y = add y (and y x)", op(0, op(1, v(0), v(1)), v(1)), op(0, v(1), op(1, v(1), v(0)))),
    ] {
        let (p, s) = rewrite_law(job, n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no rewrite proof"));
        job.lemmas.ck(name, &p, &s);
    }
    // associativity instances, including one that needs reordering as well
    for (name, t1, t2) in [
        ("add (add x y) y = add x (add y y)", op(0, op(0, v(0), v(1)), v(1)), op(0, v(0), op(0, v(1), v(1)))),
        ("add (add y y) x = add (add x y) y", op(0, op(0, v(1), v(1)), v(0)), op(0, op(0, v(0), v(1)), v(1))),
    ] {
        let (p, s) = rewrite_law(job, n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no rewrite proof"));
        job.lemmas.ck(name, &p, &s);
    }
    // a false law is refused by the truth-table pre-check
    assert!(rewrite_law(job, n, 2, &op(0, v(0), v(1)), &op(0, v(0), v(0))).is_none());
}

#[test]
pub fn a_law_over_lemma_parameters_discharges_to_a_closed_proof() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let (p, s) = rewrite_law(job, 2, 3, &op(0, op(0, v(2), v(0)), v(1)), &op(0, v(1), op(0, v(0), v(2)))).expect("comm+assoc");
        assert!(job.lemmas.params.as_ref().is_some_and(|(.., b)| !b.is_empty()), "no lemma was bound");
        assert!(check(&Ctx::new(), &p, &s).is_err(), "a proof over lemma parameters is not closed");
        job.lemmas.ck("over parameters", &p, &s);
        // a machine proof's case lemmas are parameters too
        let add = |a: Term, b: Term| op(0, a, b);
        let (pm, sm) = add_tree_law(job, 2, 3, &add(add(v(0), v(1)), v(2)), &add(v(0), add(v(1), v(2)))).expect("assoc3");
        assert!(check(&Ctx::new(), &pm, &sm).is_err(), "the machine proof's lemmas are not parameters");
        job.lemmas.ck("machine over parameters", &pm, &sm);
        // a lemma whose proof uses lemmas bound before it: a rule proved through a machine proof
        let scopes = |job: &Job| job.lemmas.params.as_ref().map_or(0, |(_, b)| b.len());
        let before = scopes(job);
        let (l, r) = (add(op(4, v(0), v(1)), v(2)), add(op(4, v(2), v(1)), v(0)));
        let (pr, sr) = shared_lemma(job, "nested".into(), |job| prove_rule(job, 2, 3, &l, &r).expect("rule"));
        assert!(scopes(job) >= before + 2, "the rule's proof bound no lemma of its own");
        let all = apps(lam(sm, lam(shift(&s, 0, 1), lam(shift(&sr, 0, 2), var(2)))), vec![pm, p, pr]);
        ck("discharged", &discharge(job, all), &sm);
    })
}

#[test]
pub fn a_second_discharge_in_a_job_applies_only_the_lemmas_bound_after_the_first() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let lemma = |n: usize| (good_lit(n, 0), app(good_bv(n), lit(n, 0)));
        let (ra, sa) = shared_lemma(job, "A".into(), |_| lemma(2));
        ck("A", &discharge(job, ra), &sa);
        let (rb, sb) = shared_lemma(job, "B".into(), |_| lemma(3));
        assert!(discharge(job, rb) == app(lam(sb, var(0)), lemma(3).0), "the second discharge applies B's proof alone");
        // A asked for again after a discharge is bound afresh, not the ended scope's parameter
        let (ra, _) = shared_lemma(job, "A".into(), |_| lemma(2));
        ck("A again", &discharge(job, ra), &sa);
    })
}

#[test]
pub fn carry_chain_builder_finds_the_constant_carry() {
    let v = |i: usize| Term::v(i);
    let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("add x (xor x -1) = -1", op(0, v(0), op(3, v(0), Term::ONES)), Term::ONES),
            ("add (xor -1 y) y = -1", op(0, op(3, Term::ONES, v(1)), v(1)), Term::ONES),
            ("add x 0 = x", op(0, v(0), Term::ZERO), v(0)),
            ("add (and x 0) y = y", op(0, op(1, v(0), Term::ZERO), v(1)), v(1)),
        ] {
            let (p, s) = carry_chain_law(n, &t1, &t2).unwrap_or_else(|| panic!("{name}: no constant carry"));
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        // no constant carry exists for these
        assert!(carry_chain_law(n, &op(0, v(0), v(1)), &op(0, v(1), v(0))).is_none());
        assert!(carry_chain_law(n, &op(0, v(0), Term::ONES), &v(0)).is_none());
    }
}

// ---- Searching for the carry-state encoding (search note sections 14 and 15). A sum tree of `c + 1` leaves (each
// leaf an add-free bitwise term over `k` vectors) is a ripple machine with `c` carries, one per `add` node. Two
// such sums agree if some encoding phi = (phi_1..phi_m) of the carry vector (m Boolean functions of the `c`
// carries) carries enough information: each side's output bit and next phi-values must be functions of (the `k`
// operand bits, phi(carries)), the same functions on both sides. `moore_encoding` computes the coarsest one by partition
// refinement; the proof is the associativity proof with the discovered phi in
// place of the hand-derived (xor, and) -- for a three-leaf sum, the total carry in binary.

/// A rule proved inside a rewrite (`proving`) runs with its rule blocked and as a rewriting job of its own: the caller's
/// budget, trace, fallbacks and blocked rules are as before.
#[test]
fn proving_leaves_the_callers_rewrite_state() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        (job.rw.budget, job.rw.trace, job.rw.fallbacks) = (777, Some(vec![]), 5);
        let blocked = job.blocked.len();
        let (l, r) = (parse_term("shr1(xor(x, -1), 0)"), parse_term("xor(shr1(x, 0), shr1(-1, 0))"));
        let inner = proving(job, &[(l, r)], |job| {
            let blocked = job.blocked.len();
            (blocked, rewrite_law(job, 4, 1, &l, &r).is_some())
        });
        assert_eq!(inner, (blocked + 1, true));
        assert_eq!((job.rw.budget, job.rw.trace.as_ref().map(Vec::len), job.rw.fallbacks, job.blocked.len()), (777, Some(0), 5, blocked));
    })
}

/// sbo3's rewrite cycle (docs/tier-cycle.md, "Why ordered sbo3 still cycled"): two rules and a permutative one bring
/// `sub(sub(z, x), sub(y, z))` back to itself. `rewrite` cuts it, so the law is proved without using up the step budget, and the
/// proof checks.
/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn rewrite_cycles_are_cut() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    tatic_kernel::scoped(|| {
        let rules = "sub(sub(x, y), z) -> sub(x, add(y, z))\nadd(x, sub(y, z)) -> sub(x, sub(z, y))\nsub(x, sub(y, z)) -> sub(z, sub(y, x))\n";
        let (t1, t2) = (parse_term("sub(sub(z, x), sub(y, z))"), parse_term("sub(add(z, z), add(x, y))"));
        let (out, spent) = job.measured(LAW_STEPS, |job| job.with_mined(parse_rules(rules), |job| rewrite_law(job, 4, 3, &t1, &t2)));
        let (cuts, left) = (spent.cycle_cuts, LAW_STEPS - spent.steps);
        println!("cuts {cuts}, budget left {left}, proved {}", out.is_some());
        assert!(cuts > 0, "no cycle cut");
        assert!(left > 0, "the step budget ran out");
        let (p, s) = out.expect("proved");
        job.lemmas.ck("cycle law", &p, &s);
    })
}

/// cmp3d's growing chain (docs/tier-cycle.md, "Growth cut"): the two rules rewrite into each other and each lap copies the first
/// argument in, so no term repeats. The term on the path embeds in its larger copy, and the cut ends the chain there instead of at
/// the budget (which it runs out with only the repeat cut).
/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn growing_rewrite_chains_are_cut() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    tatic_kernel::scoped(|| {
        let rules = "lt(x, sub(y, z)) -> lt(x, add(sub(x, y), z))\nlt(x, add(y, z)) -> lt(x, sub(sub(x, y), z))\n";
        let (t1, t2) = (parse_term("lt(z, add(add(x, x), y))"), parse_term("lt(z, add(y, add(x, x)))"));
        let (out, spent) = job.measured(LAW_STEPS, |job| job.with_mined(parse_rules(rules), |job| rewrite_law(job, 4, 3, &t1, &t2)));
        let (cuts, left) = (spent.cycle_cuts, LAW_STEPS - spent.steps);
        println!("cuts {cuts}, budget left {left}, proved {}", out.is_some());
        assert!(cuts > 0, "no growth cut");
        assert!(left > 0, "the step budget ran out");
        if let Some((p, s)) = out {
            job.lemmas.ck("growth law", &p, &s);
        }
    })
}

/// `RewriteMemo::filtered`: a memo built under some rules keeps its results under one more rule, tried last, for the entries whose
/// traces that rule's left side matches at no term where no rule fired; the rule miner seeds each candidate's scoring with them. The whole memo would replay
/// results the extra rule changes.
/// A pattern matches a term only where the term's shape has every bit the pattern needs, so a trace whose shapes lack one
/// can be skipped (docs/tier-cycle.md, "Survey: the next lever"); and the filter does reject.
#[test]
fn shapes_hold_every_bit_a_matching_pattern_needs() {
    let rules = parse_rules("sub(sub(x, y), z) -> sub(x, add(y, z))\nor(x, and(x, y)) -> x\nadd(x, 0) -> x\nxor(x, x) -> 0\nand(-1, x) -> x\nx -> x\n");
    let mut subs = vec![];
    for t in ["sub(sub(add(x, y), z), sub(x, 0))", "or(and(x, y), and(x, and(x, y)))", "xor(add(x, 0), add(x, 0))", "and(-1, -1)", "sub(x, add(y, z))"] {
        parse_term(t).subterms(&mut subs);
    }
    let mut matched = 0;
    for (l, _) in &rules {
        for t in &subs {
            if matches(l, t) {
                matched += 1;
                assert_eq!(t.shape() & l.needs(), l.needs(), "{} matches {} but its shape lacks a needed bit", l.show(), t.show());
            }
        }
    }
    assert!(matched > rules.len(), "every rule matches somewhere");
    let (l, t) = (parse_term("and(x, or(y, z))"), parse_term("and(x, y)"));
    assert_ne!(t.shape() & l.needs(), l.needs(), "an or child is needed and missing");
}

/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn filtered_memo_entries_hold_under_an_extra_rule() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    let (n, kv) = (4, 3);
    let terms: Vec<Term> =
        ["sub(sub(z, x), sub(y, z))", "add(sub(x, y), sub(add(y, z), x))", "sub(add(x, y), sub(z, x))", "or(sub(x, y), and(sub(x, y), z))"].iter().map(|s| parse_term(s)).collect();
    let base = parse_rules("sub(add(x, y), z) -> add(sub(x, z), y)\n");
    // every term rewritten under `rules` with `memo` in force: the normal forms, the steps used, and the memo afterwards
    let run = |job: &mut Job, rules: &[(Term, Term)], memo: RewriteMemo| {
        job.rw.memo = Some(memo);
        job.rw.trace = Some(vec![]);
        let out: Vec<(String, i64)> = job.with_mined(rules.to_vec(), |job| {
            terms
                .iter()
                .map(|t| {
                    let (nf, spent) = job.measured(LAW_STEPS, |job| rewrite(job, t, n, kv).0.show());
                    (nf, spent.steps)
                })
                .collect()
        });
        job.rw.trace = None;
        (out, job.rw.memo.take().unwrap())
    };
    let (before, memo) = run(job, &base, RewriteMemo::new(kv));
    for extra in ["sub(sub(x, y), z) -> sub(x, add(y, z))\n", "or(x, and(x, y)) -> x\n"] {
        let rules: Vec<(Term, Term)> = base.iter().cloned().chain(parse_rules(extra)).collect();
        let l = &rules.last().unwrap().0;
        let seed = memo.filtered(|tr| !tr.touched_by(rules.last().unwrap(), |fired| fired.preempted_by(|f| run_order(l, &rules.last().unwrap().1) < run_order(&f.0, &f.1))));
        assert!(!seed.map.is_empty() && seed.map.len() < memo.map.len(), "{extra}: the filter kept {} of {}", seed.map.len(), memo.map.len());
        let fresh = run(job, &rules, RewriteMemo::new(kv)).0;
        assert_eq!(run(job, &rules, seed).0, fresh, "{extra}");
        // the unfiltered memo would replay `before` (debug builds reject such a replay, `check_replay`)
        assert_ne!(before, fresh, "{extra}: the extra rule changes nothing here");
    }
}

/// The join's trace under `rules`: the terms `join_eq` recorded (`Fired::Join`) and whether it met.
fn join_trace(job: &mut Job, a: &str, b: &str, rules: &str) -> (bool, Trace) {
    job.rw.trace = Some(vec![]);
    let met = job.with_mined(parse_rules(rules), |job| join_eq(job, 4, 3, &parse_term(a), &parse_term(b)).is_some());
    (met, Trace::new(job.rw.trace.take().unwrap()))
}

/// A join that fails records every term it examined (`Fired::Join`), so a candidate that could make it meet is seen: in the
/// join a rule acts wherever either usable side matches, here at a term no rewrite of the two sides asks about.
#[test]
fn failed_join_traces_every_term_it_examines() {
    let job = &mut Job::new(Setup::process());
    let (a, b) = ("sub(x, y)", "sub(0, sub(y, x))");
    let (met, joined) = join_trace(job, a, b, "");
    assert!(!met);
    // ~(y - x) = x - y - 1, at `xor(sub(y, x), -1)`, a step from `sub(0, sub(y, x))`
    let rule = parse_rules("xor(sub(x, y), -1) -> add(sub(y, x), -1)\n")[0];
    let sides = Trace::new(vec![(parse_term(a), Fired::None), (parse_term(b), Fired::None)]);
    assert!(!sides.touched_by(&rule, |_| true), "the rule's left side matches neither side");
    assert!(joined.touched_by(&rule, |_| true), "the join examined a term the rule's left side matches");
    let back = (parse_term("and(x, or(y, x))"), rule.0);
    assert!(joined.touched_by(&back, |_| true), "a rule whose right side matches there acts backward");
    assert!(!Trace::new(joined.items().iter().map(|(t, _)| (*t, Fired::None)).collect()).touched_by(&back, |_| true), "but not in a rewrite");
    assert!(!joined.touched_by(&parse_rules("or(x, and(x, y)) -> x\n")[0], |_| true), "no or anywhere, and x cannot be a step's start");
}

/// A join that meets records only the terms on its path (what the search examined at them), where the rules its plan used
/// fired: a rule added elsewhere leaves the plan a proof (the miner's error is a search that more rules would push past the
/// visit cap, docs/decisions/2026-10-17-monotone-join.md), and a rule it used, removed, touches the trace.
#[test]
fn met_join_traces_its_path_only() {
    let job = &mut Job::new(Setup::process());
    let (a, b) = ("add(add(z, y), sub(x, -1))", "add(sub(add(x, y), -1), z)");
    let (met, joined) = join_trace(job, a, b, "");
    assert!(met);
    for t in [a, b] {
        assert!(joined.items().iter().any(|(u, _)| *u == parse_term(t)), "{t} is on the path");
    }
    // -(~x) = x + 1, at `sub(0, xor(x, -1))`, a term the search examined off its path
    assert!(!joined.touched_by(&parse_rules("sub(0, xor(x, -1)) -> sub(0, sub(-1, x))\n")[0], |_| true));
    let rule = "or(x, y) -> add(xor(x, y), and(x, y))\n";
    let (met, joined) = join_trace(job, "or(x, y)", "add(xor(x, y), and(x, y))", rule);
    assert!(met);
    assert!(joined.touched_by(&parse_rules(rule)[0], |_| true), "the plan used the rule");
}

/// `TraceIndex::touched` gives the traces `Trace::touched_by` accepts, for rules matching forward, backward and nowhere, and
/// for a condition on the fired rule.
/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn trace_index_agrees_with_touched_by() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    let (n, kv) = (4, 3);
    let mut traces: Vec<Trace> = [("sub(x, y)", "sub(0, sub(y, x))"), ("add(add(z, y), sub(x, -1))", "add(sub(add(x, y), -1), z)"), ("xor(xor(x, y), z)", "xor(z, xor(y, x))")]
        .iter()
        .map(|(a, b)| join_trace(job, a, b, "").1)
        .collect();
    for t in ["sub(sub(x, y), and(x, y))", "or(and(x, y), xor(x, -1))", "add(x, sub(0, x))", "xor(or(x, y), and(x, y))"] {
        job.rw.trace = Some(vec![]);
        rewrite(job, &parse_term(t), n, kv);
        traces.push(Trace::new(job.rw.trace.take().unwrap()));
    }
    traces.push(Trace::default());
    let index = TraceIndex::new(&traces);
    // rules whose sides are the traces' own terms (each matches itself) and patterns with variables
    let mut terms: Vec<Term> = traces.iter().flat_map(|tr| tr.items().iter().map(|(t, _)| *t)).collect();
    terms.sort();
    terms.dedup();
    let mut rules: Vec<(Term, Term)> = terms.iter().step_by(7).zip(terms.iter().skip(3).step_by(11)).map(|(l, r)| (*l, *r)).collect();
    rules.extend(parse_rules("xor(sub(x, y), -1) -> add(sub(y, x), -1)\nor(x, and(x, y)) -> x\nsub(x, y) -> add(x, sub(0, y))\nadd(x, y) -> add(y, x)\n"));
    rules.push((parse_term("and(x, or(y, x))"), parse_term("xor(sub(x, y), -1)")));
    rules.extend(parse_rules("and(and(and(x, y), z), and(x, y)) -> and(x, and(y, z))\nor(or(x, -1), or(y, -1)) -> -1\n"));
    let (mut some, mut none, mut narrowed) = (0, 0, 0);
    for rule in &rules {
        let mut got = vec![];
        for also in [&(|_: &Fired| true) as &dyn Fn(&Fired) -> bool, &|f: &Fired| *f != Fired::Fixed, &|f: &Fired| *f == Fired::Join] {
            let want: Vec<usize> = (0..traces.len()).filter(|&i| traces[i].touched_by(rule, also)).collect();
            assert_eq!(index.touched(rule, also), want, "{} -> {}", rule.0.show(), rule.1.show());
            if want.is_empty() { none += 1 } else { some += 1 }
            got.push(want);
        }
        narrowed += (got[0] != got[2]) as usize;
    }
    assert!(some > 20 && none > 5 && narrowed > 3, "touched {some}, untouched {none}, narrowed by the condition {narrowed}");
}

/// Join results are kept in `RewriteMemo` with the terms each search examined: under an extra rule `filtered` keeps the entries
/// the rule touches nowhere, and they give what a fresh search would; a hit gives the stored result.
#[test]
fn filtered_join_entries_hold_under_an_extra_rule() {
    let job = &mut Job::new(Setup::process());
    let (n, kv) = (4, 3);
    let pairs: Vec<(Term, Term)> = [("or(x, y)", "add(xor(x, y), and(x, y))"), ("xor(xor(x, y), z)", "xor(z, xor(y, x))")]
        .iter()
        .map(|(a, b)| (parse_term(a), parse_term(b)))
        .collect();
    let run = |job: &mut Job, rules: Vec<(Term, Term)>, memo: RewriteMemo| {
        job.rw.memo = Some(memo);
        let out: Vec<bool> = job.with_mined(rules, |job| pairs.iter().map(|(a, b)| join_eq(job, n, kv, a, b).is_some()).collect());
        (out, job.rw.memo.take().unwrap())
    };
    let (before, memo) = run(job, vec![], RewriteMemo::new(kv));
    assert_eq!(memo.joins.len(), pairs.len());
    assert_eq!(run(job, vec![], memo.filtered(|_| true)).0, before, "hits");
    let rule = parse_rules("or(x, y) -> add(xor(x, y), and(x, y))\n")[0];
    let seed = memo.filtered(|tr| !tr.touched_by(&rule, |_| true));
    assert_eq!(seed.joins.len(), 1, "the xor pair's search met no or, nor xor beside and under add");
    let fresh = run(job, vec![rule], RewriteMemo::new(kv)).0;
    assert_eq!(run(job, vec![rule], seed).0, fresh);
    assert_ne!(before, fresh, "the rule joins the first pair");
}

/// `Job::join_cost` counts the searches run, the terms they reached and the ones that met; a memo hit runs none and counts as a hit.
#[test]
fn join_cost_counts_searches_but_not_memo_hits() {
    let job = &mut Job::new(Setup::process());
    let (a, b) = (parse_term("xor(xor(x, y), z)"), parse_term("xor(z, xor(y, x))"));
    job.rw.memo = Some(RewriteMemo::new(3));
    let (first, s1) = job.spent(|job| join_eq(job, 4, 3, &a, &b).is_some());
    let (second, s2) = job.spent(|job| join_eq(job, 4, 3, &a, &b).is_some());
    job.rw.memo.take();
    assert!(first && second);
    assert_eq!((s1.join.searches, s1.join.met), (1, 1));
    assert!(s1.join.reached >= 2, "both sides at least");
    assert_eq!(s2.join, JoinCost { hits: 1, ..JoinCost::default() }, "the second call was a hit");
    assert!(s1.join.nanos > 0 && s1.join.failed_nanos == 0, "a met search's time counts, not as failed");
    // an equal pair the join cannot close (`failed_join_traces_every_term_it_examines`)
    let (closed, s3) = job.spent(|job| join_eq(job, 4, 3, &parse_term("sub(x, y)"), &parse_term("sub(0, sub(y, x))")).is_some());
    assert!(!closed && s3.join.met == 0 && s3.join.failed_nanos > 0 && s3.join.nanos == s3.join.failed_nanos);
}

/// The join store serves a pair it holds a path for, with a plan the kernel accepts (and by counting, `Rules::counting`),
/// without a search; it serves none once a law on the path leaves the table, and no job without a store is served.
#[test]
fn join_store_serves_a_stored_path_under_its_laws_only() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let rule = (parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"));
        let (n, k) = (4, 3);
        let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
        let join = |job: &mut Job| {
            job.rw.memo = Some(RewriteMemo::new(k));
            let (plan, spent) = job.spent(|job| join_eq(job, n, k, &a, &b));
            job.rw.memo.take();
            (plan, spent.join.searches, spent.join.stored)
        };
        job.with_mined(vec![rule], |job| {
            assert!(matches!(join(job), (Some(_), 1, 0)), "no store: searched");
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            assert!(matches!(join(job), (Some(_), 1, 0)), "an empty store: searched, and the path fed");
            let (plan, searches, stored) = join(job);
            assert_eq!((searches, stored), (0, 1), "served from the store");
            let plan = plan.expect("a stored join");
            assert!(Compiler::new(n, k).proof(job, &plan).0 == a && Compiler::new(n, k).proof(job, &plan).1 == b);
            let (p, s) = law_proof(job, n, k, &a, &b, &plan);
            job.lemmas.ck("stored", &p, &s);
            let counting = job.rules().counting(true);
            let (counted, _, stored) = job.with_rules(counting, |job| join(job));
            assert!(matches!(counted.as_deref(), Some(Plan::Counting)) && stored == 1, "counting is served too");
        });
        assert_eq!(join(job).2, 0, "the rule left: no stored path");
        job.join_store = None;
    })
}

/// A cached failed search stands only while the join store has no path for its pair: the store grows as searches feed it,
/// and a failure cached before (in a seeded memo, `RewriteMemo::filtered`) hid a path the miner's scoring workers saw, so a
/// mine re-chose a rule it had for each round's phantom gain (run 2026-10-22-hidden-twins-2, 8631 rounds).
#[test]
fn a_cached_failed_join_yields_to_a_stored_path() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let (n, k) = (4, 3);
        let rule = (parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"));
        let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
        job.with_mined(vec![rule], |job| {
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            job.rw.memo = Some(RewriteMemo::new(k));
            assert!(join_eq(job, n, k, &a, &b).is_some(), "searched, and the path fed");
            let mut stale = RewriteMemo::new(k);
            stale.joins.insert((a, b), std::rc::Rc::new((None, Trace::default())));
            job.rw.memo = Some(stale);
            let (plan, spent) = job.spent(|job| join_eq(job, n, k, &a, &b));
            assert!(plan.is_some() && spent.join.stored == 1, "served from the store over the cached failure");
            assert!(job.rw.memo.take().unwrap().joins[&(a, b)].0.is_some(), "the memo now holds the met join");
            job.join_store = None;
        })
    })
}

/// A worker reads the store as it was frozen: what the feeding job adds later is not in its copy.
#[test]
fn join_store_workers_read_the_frozen_copy() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let k = 3;
        job.with_mined(vec![(parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"))], |job| {
            let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
            let (c, d) = (parse_term("xor(xor(x, y), z)"), parse_term("xor(z, xor(y, x))"));
            let join = move |job: &mut Job, x: &Term, y: &Term| {
                job.rw.memo = Some(RewriteMemo::new(k));
                let (joined, spent) = job.spent(|job| join_eq(job, 4, k, x, y));
                assert!(joined.is_some());
                job.rw.memo.take();
                spent.join.stored
            };
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            join(job, &a, &b);
            let frozen = job.join_store.as_ref().and_then(JoinStoreUse::frozen).expect("the job feeds a store");
            join(job, &c, &d);
            let rules = job.rules().mined().to_vec();
            let setup = job.setup().clone();
            let worker = std::thread::spawn(move || {
                let job = &mut Job::new(setup);
                tatic_kernel::scoped(|| {
                    job.with_mined(rules, |job| {
                        job.join_store = Some(JoinStoreUse::Read(frozen));
                        (join(job, &a, &b), join(job, &c, &d))
                    })
                })
            });
            assert_eq!(worker.join().unwrap(), (1, 0), "the pair joined before the freeze is served, the one after is not");
            assert_eq!(join(job, &c, &d), 1, "the feeding job reads its own store");
            job.join_store = None;
        })
    })
}

/// A stored path is served read either way, through several steps, and after its law moves to another index in the table;
/// the kernel accepts each plan.
#[test]
fn join_store_serves_paths_backwards_through_several_steps_and_moved_laws() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let (n, k) = (4, 3);
        let rule = (parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"));
        let other = (parse_term("sub(x, sub(x, y))"), parse_term("y"));
        let pairs = [
            (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)")),
            (parse_term("xor(xor(x, y), z)"), parse_term("xor(z, xor(y, x))")),
        ];
        let served = |job: &mut Job, a: &Term, b: &Term| {
            job.rw.memo = Some(RewriteMemo::new(k));
            let (plan, spent) = job.spent(|job| join_eq(job, n, k, a, b));
            let plan = plan.expect("joined");
            job.rw.memo.take();
            let (p, s) = law_proof(job, n, k, a, b, &plan);
            job.lemmas.ck("stored", &p, &s);
            spent.join.stored
        };
        let before = job.with_mined(vec![rule], |job| {
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            for (a, b) in &pairs {
                served(job, a, b);
            }
            let (c, d) = &pairs[1];
            assert!(stored_join(job, *d, *c).expect("stored").1.len() > 2, "the xor pair's path has several steps");
            job.rules().table.join_key.clone()
        });
        job.with_mined(vec![other, rule], |job| {
            let after = &job.rules().table.join_key;
            assert!(before.iter().any(|(law, i)| after.get(law).is_some_and(|j| j != i)), "a law moved");
            for (a, b) in &pairs {
                assert_eq!((served(job, b, a), served(job, a, b)), (1, 1), "served backwards and forwards, the rule moved");
            }
        });
        job.join_store = None;
    })
}

/// A search feeds the store only where the store is read (the memo on, no rule blocked): the miner's proofs run on its main
/// thread at 1 thread and on others otherwise, so a store they fed would depend on the thread count.
#[test]
fn join_store_is_fed_only_where_it_is_read() {
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
        let k = 3;
        let rule = (parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"));
        job.with_mined(vec![rule], |job| {
            let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
            let join = |job: &mut Job, memo: bool| {
                job.rw.memo = memo.then(|| RewriteMemo::new(k));
                let (joined, spent) = job.spent(|job| join_eq(job, 4, k, &a, &b));
                assert!(joined.is_some());
                job.rw.memo.take();
                spent.join.stored
            };
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            join(job, false);
            job.blocked.push(rule);
            join(job, true);
            job.blocked.clear();
            assert_eq!(join(job, true), 0, "searched without the memo and while proving: neither fed the store");
            assert_eq!(join(job, true), 1, "searched with the memo: fed");
            job.join_store = None;
        })
    })
}

/// A memo hit gives what a fresh rewrite would, also under rules that cycle: an entry made where the path was short is replayed
/// inside a call that a fresh rewrite would cut (docs/tier-cycle.md, the law 168 entry under Open).
#[test]
fn memo_hits_match_fresh_rewrites_under_cycling_rules() {
    let job = &mut Job::new(Setup::process());
    let (n, kv) = (4, 3);
    // t = lt(x, sub(y, z)) -> u = lt(x, add(y, z)) -> v = lt(x, or(sub(y, z), y)) -> lt(x, and(..)): t embeds in v, so rewriting t
    // cuts at v, while u on its own (rewritten first, into the memo) does not
    // and t again, replayed from its own entry (its cut was against itself), then u, whose entry made inside t's call is not kept
    let terms: Vec<Term> = ["lt(x, add(y, z))", "lt(x, sub(y, z))", "lt(x, sub(y, z))", "lt(x, add(y, z))"].iter().map(|s| parse_term(s)).collect();
    let rules = "lt(x, sub(y, z)) -> lt(x, add(y, z))\nlt(x, add(y, z)) -> lt(x, or(sub(y, z), y))\nlt(x, or(y, z)) -> lt(x, and(y, z))\n";
    let (fresh, memo) = job.with_mined(parse_rules(rules), |job| {
        let mut run = |memo: Option<RewriteMemo>| {
            job.rw.memo = memo;
            let out: Vec<(String, i64)> = terms
                .iter()
                .map(|t| {
                    let (nf, spent) = job.measured(LAW_STEPS, |job| rewrite(job, t, n, kv).0.show());
                    (nf, spent.steps)
                })
                .collect();
            job.rw.memo.take();
            out
        };
        (run(None), run(Some(RewriteMemo::new(kv))))
    });
    let differ: Vec<_> = terms.iter().zip(fresh.iter().zip(&memo)).filter(|(_, (f, m))| f != m).map(|(t, (f, m))| format!("{}: fresh {f:?} memo {m:?}", t.show())).collect();
    assert!(differ.is_empty(), "{} of {} differ:\n{}", differ.len(), terms.len(), differ.join("\n"));
}

/// A rewrite whose cuts were all against terms its own call took up is kept: any replay cuts them again. One cut against a
/// term further out is not (docs/tier-cycle.md, "Survey: `rewrite_memo`'s 17.4% of CPU").
/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn memo_keeps_rewrites_cut_inside_their_own_call() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    let (n, kv) = (4, 3);
    // rewriting t goes t -> u -> v, where t embeds in v: the cut is against t itself; u's own call, inside t's, is cut by t
    let (t, u) = (parse_term("lt(x, sub(y, z))"), parse_term("lt(x, add(y, z))"));
    let rules = parse_rules("lt(x, sub(y, z)) -> lt(x, add(y, z))\nlt(x, add(y, z)) -> lt(x, or(sub(y, z), y))\nlt(x, or(y, z)) -> lt(x, and(y, z))\n");
    job.rw.memo = Some(RewriteMemo::new(kv));
    let (_, spent) = job.measured(LAW_STEPS, |job| job.with_mined(rules, |job| rewrite(job, &t, n, kv)));
    let cut = spent.cycle_cuts > 0;
    let memo = job.rw.memo.take().unwrap();
    assert!(cut, "rewriting t cuts");
    assert!(memo.map.contains_key(&(n, t)), "t's rewrite, cut only against itself, is kept");
    assert!(!memo.map.contains_key(&(n, u)), "u's rewrite inside t's, cut against t, is not");
}

#[test]
pub fn refute_returns_a_witness_for_false_laws_and_none_for_true_ones() {
    let t = |s: &str| parse_term(s);
    for (l, r) in [("add(x, y)", "add(y, x)"), ("xor(x, x)", "0"), ("sub(add(x, y), y)", "x")] {
        assert!(t(l).refute(&t(r), 2).is_none(), "{l} = {r} is a law");
    }
    for (l, r) in [("lt(x, y)", "lt(y, x)"), ("sub(x, y)", "sub(y, x)"), ("and(x, y)", "or(x, y)"), ("shl1(x, 0)", "x")] {
        let (l, r) = (t(l), t(r));
        let (w, vals) = l.refute(&r, 2).unwrap_or_else(|| panic!("{} = {} is false", l.show(), r.show()));
        assert_ne!(l.interp(w, &vals), r.interp(w, &vals), "witness for {} = {}", l.show(), r.show());
    }
}

#[test]
fn term_interning() {
    let (x, y) = (Term::v(0), Term::v(1));
    let a = Term::op(ADD, x, Term::op(XOR, y, Term::ONES));
    let b = Term::op(ADD, x, Term::op(XOR, y, Term::ONES));
    assert!(std::ptr::eq(a.node(), b.node()));
    assert!(a != Term::op(ADD, Term::op(XOR, y, Term::ONES), x));
    // built on 8 threads at once: one node per term
    let built: Vec<Vec<Term>> = std::thread::scope(|s| {
        let hs: Vec<_> = (0..8)
            .map(|_| s.spawn(|| (0..200).map(|i| Term::op(i % 8, Term::v(i % 5), Term::op(AND, Term::v(i % 7), Term::ZERO))).collect::<Vec<_>>()))
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    for w in &built[1..] {
        assert!(w.iter().zip(&built[0]).all(|(p, q)| std::ptr::eq(p.node(), q.node())));
    }
    assert_eq!((std::mem::size_of::<Term>(), std::mem::size_of::<Node>()), (8, 32));
}

#[test]
fn term_attributes_match_a_walk() {
    fn walk(t: &Term) -> (usize, Vec<usize>) {
        match *t.node() {
            Node::V(i) => (1, vec![i]),
            Node::Op(_, a, b) => {
                let ((sa, mut va), (sb, vb)) = (walk(&a), walk(&b));
                va.extend(vb);
                (1 + sa + sb, va)
            }
            _ => (1, vec![]),
        }
    }
    let high = Term::op(XOR, Term::op(AND, Term::v(63), Term::v(9)), Term::v(40));
    let ts: Vec<Term> = PIN_SOURCE.iter().map(|s| parse_term(s)).chain([high, Term::ZERO, Term::ONES, Term::v(0)]).collect();
    for t in &ts {
        let (size, vars) = walk(t);
        assert_eq!(t.size(), size, "{}", t.size());
        assert_eq!(t.max_var(), vars.iter().copied().max().unwrap_or(0));
        assert!((0..70).all(|v| t.has_var(v) == vars.contains(&v)));
    }
}

#[test]
fn rule_table_lists_every_matching_rule_in_order() {
    let job = &Job::new(Setup::process());
    // built-in rules plus run-time ones with a variable, a leaf and a nested operand at the root's operands
    let mined = parse_rules("x -> and(x, x)\nsub(0, x) -> x\nadd(sub(x, y), z) -> sub(add(x, z), y)\n");
    let table = RuleTable::new(job.setup(), mined);
    let mut leaves: Vec<Term> = vec![Term::ZERO, Term::ONES, Term::v(0)];
    leaves.extend(terms(3, true));
    let (mut tried, mut skipped) = (0, 0);
    for t in &leaves {
        let ids: Vec<usize> = table.candidates(t).map(|(i, _)| i).collect();
        assert!(ids.windows(2).all(|w| w[0] < w[1]), "{}: out of order", t.show());
        for (i, r) in table.rules.iter().enumerate().filter(|(_, r)| !job.setup().ablated(r.name)) {
            if match_pat(&r.lhs, t, &mut [None; RULE_VARS]) {
                assert!(ids.contains(&i), "{}: {} matches but is not a candidate", t.show(), r.lhs.show());
            }
        }
        tried += ids.len();
        skipped += table.rules.len() - ids.len();
    }
    assert!(skipped > 0 && tried > 0, "{tried} tried, {skipped} skipped");
}

/// `PatIndex::get` offers every pattern that matches a term, and for a pattern whose repeated variables all lie within
/// depth 2 only those: it checks the shape down to the grandchildren, a leaf's own class, and that the positions within
/// depth 2 holding one variable hold one subterm.
#[test]
fn pat_index_offers_only_matches_down_to_grandchildren() {
    let pats = ["and(x, or(y, 0))", "and(x, or(y, z))", "0", "add(x, x)", "y", "-1", "or(and(x, -1), y)", "or(and(x, y), and(y, x))", "or(x, and(x, 0))"];
    let pats: Vec<Term> = pats.map(parse_term).to_vec();
    let ix = PatIndex::new(pats.iter().enumerate().map(|(i, p)| (i, p, ())));
    let mut terms = vec![Term::v(0), Term::v(1), Term::ZERO, Term::ONES];
    for _ in 0..2 {
        let level: Vec<Term> = terms.iter().flat_map(|&a| terms.iter().flat_map(move |&b| [ADD, AND, OR].map(|o| Term::op(o, a, b)))).collect();
        terms.extend(level);
    }
    let mut matched = vec![0; pats.len()];
    for t in &terms {
        let offered: Vec<usize> = ix.get(t).map(|(i, ())| i).collect();
        for (i, p) in pats.iter().enumerate() {
            let m = match_pat(p, t, &mut [None; RULE_VARS]);
            assert!(m == offered.contains(&i), "{} {} {} but is{} offered", p.show(), if m { "matches" } else { "does not match" }, t.show(), if m { " not" } else { "" });
            matched[i] += m as usize;
        }
    }
    assert!(matched.iter().all(|&m| m > 0) && matched.iter().sum::<usize>() > 1000, "matched {matched:?}");
}

#[test]
fn value_memo_matches_interp() {
    // the screen as it was before `ValueMemo`: both sides evaluated on each tuple in turn
    fn old_counterexample(a: &Term, b: &Term, n: usize, k: usize, tries: usize) -> Option<Vec<u128>> {
        let mask = low_bits(n);
        let mut seed = 0x9e37_79b9_7f4a_7c15u128;
        (0..tries).find_map(|i| {
            let vals: Vec<u128> = (0..k)
                .map(|_| {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    match i {
                        0 => 0,
                        1 => mask,
                        _ => (seed >> 40) & mask,
                    }
                })
                .collect();
            (a.interp(n, &vals) != b.interp(n, &vals)).then_some(vals)
        })
    }
    let ts: Vec<Term> = PIN_SOURCE.iter().map(|s| parse_term(s)).chain([Term::ZERO, Term::ONES]).collect();
    let k = ts.iter().map(|t| t.max_var() + 1).max().unwrap();
    for n in [1, 4, 64, 128] {
        for a in &ts {
            for b in &ts {
                // 2 tries are the corners alone, where many distinct terms agree: a screen past `tries` would differ
                for tries in [2, 16, SCREEN_INPUTS] {
                    let old = old_counterexample(a, b, n, k, tries);
                    assert_eq!(a.differs_in(b, n, k, tries), old.is_some());
                    assert_eq!(a.counterexample_in(b, n, k, tries), old, "{} vs {} at {n}", a.show(), b.show());
                }
            }
        }
    }
    let mut memo = ValueMemo::exhaustive(3, 2);
    for t in ts.iter().filter(|t| t.max_var() < 2) {
        let want: Vec<u8> = (0..64u128).map(|i| t.interp(3, &[i & 7, i >> 3]) as u8).collect();
        assert_eq!(memo.values(t), want, "{}", t.show());
    }
}

/// `exhaustive`'s inputs are built once per width and variable count and shared (`bitwise_holds` asks for five widths
/// on every call).
#[test]
fn exhaustive_inputs_are_built_once() {
    let (a, b, c) = (ValueMemo::exhaustive(3, 2), ValueMemo::exhaustive(3, 2), ValueMemo::exhaustive(3, 3));
    assert_eq!(a.vars.as_ptr(), b.vars.as_ptr());
    assert_ne!(a.vars.as_ptr(), c.vars.as_ptr());
}

/// Every operator through `zip_op`, on byte and `u128` vectors, against the operator worked out a bit at a time (a ripple
/// carry for add, sub and lt): all pairs of inputs at widths 1 to 8, sampled ones at wider widths on `u128` only.
#[test]
fn operators_match_a_bit_at_a_time() {
    fn by_bits(o: usize, x: u128, y: u128, n: usize) -> u128 {
        let bit = |v: u128, i: usize| i < n && v >> i & 1 == 1;
        let name = OP_INFO[o].name;
        // add, and x - y as x + !y + 1, whose carry out says x >= y
        let mut carry = name == "sub" || name == "lt";
        let mut out = 0;
        for i in 0..n {
            let (a, b) = (bit(x, i), bit(y, i) != (name == "sub" || name == "lt"));
            let r = match name {
                "add" | "sub" | "lt" => {
                    let s = (a != b) != carry;
                    carry = a && b || carry && a != b;
                    s
                }
                "and" => a && b,
                "or" => a || b,
                "xor" => a != b,
                "shl1" => i > 0 && bit(x, i - 1),
                "shr1" => bit(x, i + 1),
                _ => panic!("no bit-at-a-time {name}"),
            };
            out |= (r as u128) << i;
        }
        if name == "lt" { !carry as u128 } else { out }
    }
    fn check<W: Word>(o: usize, n: usize, xs: &[u128], ys: &[u128]) {
        let (x, y): (Vec<W>, Vec<W>) = (xs.iter().map(|&v| W::of(v)).collect(), ys.iter().map(|&v| W::of(v)).collect());
        // from 1 the length is odd, so the loop's scalar tail runs after its vector body
        for s in [0, 1] {
            let mut out = vec![W::of(0); x.len() - s];
            zip_op(o, &mut out, &x[s..], &y[s..], low_bits(n));
            for (i, v) in out.iter().enumerate() {
                let (a, b) = (xs[s + i], ys[s + i]);
                assert_eq!(v.get(), by_bits(o, a, b, n), "{} {a} {b} at width {n} in {}", OP_INFO[o].name, std::any::type_name::<W>());
            }
        }
    }
    for o in 0..OP_INFO.len() {
        for n in 1..=8 {
            let (xs, ys): (Vec<u128>, Vec<u128>) = (0..1u128 << 2 * n).map(|i| (i & low_bits(n), i >> n)).unzip();
            check::<u8>(o, n, &xs, &ys);
            check::<u128>(o, n, &xs, &ys);
        }
        for n in [16, 64, 127, 128] {
            let m = low_bits(n);
            let mut seed = 0x9e37_79b9_7f4a_7c15u128;
            let vals: Vec<u128> = [0, 1, 2, m - 1, m, m >> 1, (m >> 1) + 1]
                .into_iter()
                .chain((0..25).map(|_| {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    seed.reverse_bits() & m
                }))
                .collect();
            let (xs, ys): (Vec<u128>, Vec<u128>) = vals.iter().flat_map(|&a| vals.iter().map(move |&b| (a, b))).unzip();
            check::<u128>(o, n, &xs, &ys);
        }
    }
}

/// A variable's vector of another length would misalign the memo's blocks, and `fill` could then write past one.
#[test]
#[should_panic(expected = "variable vector of length 3, not 4")]
fn value_memo_refuses_a_variable_of_another_length() {
    ValueMemo::<u8>::new(8, 4, [vec![0; 4].into_boxed_slice(), vec![0; 3].into_boxed_slice()].into());
}

/// `fill_op` writes every cell of its output only when its inputs are as long.
#[test]
#[should_panic(expected = "zip inputs of lengths 4 and 3 into 4")]
fn zip_op_refuses_a_shorter_input() {
    zip_op(0, &mut [0u8; 4], &[1; 4], &[2; 3], low_bits(8));
}

/// Two terms get one value class exactly when they agree on every input, asked in any order (pairs that agree here:
/// add's operands swapped, `x ^ x` and `0`, `x & -1` and `x`, `(x + y) - y` and `x`, `x << 1` and `x + x`, and the
/// comparison `x < x` and `0`: a class is values only, so callers that keep comparisons apart key on that too).
#[test]
fn value_classes_are_exact() {
    let ts: Vec<Term> = ["x", "y", "z", "0", "-1", "add(x, y)", "add(y, x)", "xor(x, x)", "and(x, -1)", "or(x, 0)",
        "sub(add(x, y), y)", "shl1(x, 0)", "add(x, x)", "xor(x, y)", "or(and(x, y), xor(x, y))", "or(x, y)", "lt(x, y)",
        "lt(y, x)", "lt(x, x)"]
    .iter()
    .map(|s| parse_term(s))
    .collect();
    let mut memo = ValueMemo::exhaustive(4, 3);
    let classes: Vec<u32> = ts.iter().rev().map(|t| memo.class(t)).collect::<Vec<_>>().into_iter().rev().collect();
    let (mut equal, mut differ) = (0, 0);
    for (a, ca) in ts.iter().zip(&classes) {
        assert_eq!(memo.class(a), *ca, "{}'s class moved", a.show());
        for (b, cb) in ts.iter().zip(&classes) {
            let same = memo.values(a).to_vec() == memo.values(b);
            assert_eq!(ca == cb, same, "{} and {}", a.show(), b.show());
            (equal, differ) = if same { (equal + 1, differ) } else { (equal, differ + 1) };
        }
    }
    assert!(equal > ts.len() && differ > 0);
}

/// `bitwise_holds` gives the per-tuple loop's answer (the one `verdict` and `prove_eq` ran before it) on add-free pairs.
#[test]
fn bitwise_holds_is_the_per_tuple_check() {
    let ts: Vec<Term> = ["x", "y", "0", "-1", "and(x, y)", "or(x, y)", "xor(x, y)", "xor(x, -1)", "shl1(x, 0)", "shr1(x, 0)",
        "shl1(and(x, y), 0)", "and(shl1(x, 0), shl1(y, 0))", "shr1(shl1(x, 0), 0)", "and(x, shr1(shl1(x, 0), 0))",
        "shr1(xor(x, z), 0)", "xor(shr1(x, 0), shr1(z, 0))", "or(and(x, y), and(x, z))", "and(x, or(y, z))"]
    .iter()
    .map(|s| parse_term(s))
    .collect();
    let old = |a: &Term, b: &Term, k: usize| {
        (1..=5usize).all(|w| (0..1u128 << (w * k)).all(|i| {
            let vals: Vec<u128> = (0..k).map(|v| (i >> (w * v)) & low_bits(w)).collect();
            a.interp(w, &vals) == b.interp(w, &vals)
        }))
    };
    let mut held = 0;
    for a in &ts {
        for b in &ts {
            let k = 1 + a.max_var().max(b.max_var());
            assert_eq!(bitwise_holds(a, b, k), old(a, b, k), "{} vs {}", a.show(), b.show());
            held += bitwise_holds(a, b, k) as usize;
        }
    }
    assert!(held > ts.len(), "some pairs other than a term with itself hold");
}
/// Sample terms in no particular order (leaves, every operator, shared and permuted subterms).
const PIN_SOURCE: [&str; 38] = [
    "add(x, add(y, z))", "x", "and(add(x, y), -1)", "-1", "add(y, x)", "q", "xor(x, -1)", "0", "add(x, y)",
    "add(add(x, y), z)", "add(x, x)", "and(x, y)", "or(x, 0)", "sub(-1, x)", "lt(x, y)", "shl1(x, x)", "shr1(y, y)",
    "add(add(x, y), y)", "add(add(x, z), y)", "and(add(x, y), 0)", "xor(and(x, y), or(x, y))", "xor(and(x, y), or(y, x))",
    "or(and(x, y), and(x, z))", "sub(add(x, y), y)", "sub(x, sub(x, y))", "lt(sub(x, y), 0)", "shl1(add(x, y), x)",
    "add(shl1(x, x), 0)", "add(0, x)", "add(-1, x)", "add(u, v)", "add(w, p)", "and(-1, 0)", "y",
    "xor(xor(x, y), xor(z, u))", "xor(xor(x, y), xor(z, v))", "add(add(add(x, y), z), u)", "add(x, add(y, add(z, u)))",
];
