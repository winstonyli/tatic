use super::*;

/// A round's candidates leave out the rules already chosen, and the rest go by bound, largest first, ties to the earlier.
#[test]
fn a_round_never_offers_a_chosen_rule() {
    let r = |l: &str, rhs: &str| (parse_term(l), parse_term(rhs));
    let provable = [r("add(0, x)", "x"), r("sub(x, x)", "0"), r("xor(x, x)", "0")];
    let bounds = [5, 9, 7];
    assert_eq!(by_bound(&provable, &[provable[1]], |i| bounds[i]), vec![(7, 2), (5, 0)]);
    assert_eq!(by_bound(&provable, &[], |i| if i == 1 { 5 } else { bounds[i] }), vec![(7, 2), (5, 0), (5, 1)]);
}

/// A winner's rival already chosen is passed over, however much it claims; the next rival that gains more and proves wins.
#[test]
fn a_round_never_offers_a_chosen_rival() {
    let r = |l: &str, rhs: &str| (parse_term(l), parse_term(rhs));
    let rivals = [r("sub(x, x)", "0"), r("sub(x, x)", "and(x, 0)"), r("sub(x, x)", "xor(x, x)")];
    let chosen = [rivals[0]];
    assert!(best_rival(&rivals, &[9, 4, 7], 3, &chosen, |_| true) == Some((rivals[2], 7)));
    assert!(best_rival(&rivals, &[9, 4, 7], 3, &chosen, |rv| *rv != rivals[2]) == Some((rivals[1], 4)));
    assert!(best_rival(&rivals, &[9, 2, 1], 3, &chosen, |_| true) == None);
}

#[test]
fn a_provers_rules_ignore_the_callers_switches() {
    let prover = Prover { rules: vec![], n: 4 };
    let job = &mut Job::new(Setup::process());
    let counting = job.rules().counting(true).tracing(true);
    let installed = job.with_rules(counting, |job| prover.install(job.setup()));
    assert!(installed.is(&installed.counting(false).tracing(false)), "a prover proves with both switches off");
}

/// The pool route looks patterns up over three variables, `lt` roots too: a pattern's group is the pool's terms equal to it on
/// every input (docs/tier-cycle/, "A pool route over three variables finds them").
#[test]
fn the_pool_finds_terms_over_three_variables() {
    let mut pool = Pool::new(4);
    let p = parse_term;
    assert!(pool.equal(&p("sub(add(x, z), add(y, z))")).contains(&p("sub(x, y)")));
    assert!(!pool.equal(&p("sub(add(x, z), add(y, z))")).contains(&p("sub(x, z)")));
    assert!(pool.equal(&p("lt(x, and(and(y, z), y))")).contains(&p("lt(x, and(y, z))")));
}

/// `classify` gives one outcome per law, in the input's order: a false equation is skipped, a law the built-in rules close
/// is clean, and the stream mine's laws (`ROLLBACK_LAWS`) leave stragglers.
#[test]
fn classify_orders_outcomes_like_the_input() {
    let named = |s: &str| {
        let (a, b) = s.split_once(" = ").unwrap();
        (s.to_string(), parse_term(a), parse_term(b))
    };
    let mut laws = vec![named("add(x, y) = add(x, z)"), named("and(x, y) = and(y, x)")];
    laws.extend(ROLLBACK_LAWS.lines().map(named));
    let job = &mut Job::new(Setup::process());
    // one letter per outcome (the kernel scope lets nothing but plain values out)
    let out: String = tatic_kernel::scoped(|| {
        classify(job, &laws, UNBOUNDED, false, false)
            .iter()
            .map(|o| match o {
                Outcome::Skipped => 'k',
                Outcome::Clean(..) => 'c',
                Outcome::Straggler(..) => 's',
            })
            .collect()
    });
    assert_eq!(out.len(), laws.len());
    assert!(out.starts_with("kc"), "a false equation is no law, and commuting `and` needs no machine proof: {out}");
    assert!(out[2..].contains('s'), "the stream mine's laws leave stragglers: {out}");
}

#[test]
fn kept_indices_keeps_the_served_laws_and_n_of_the_pool() {
    let none = |_: usize| None;
    // 3 served laws, a pool of 6, keep 2
    assert_eq!(kept_indices(9, 3, 2, &none), vec![0, 1, 2, 3, 4], "no straggler ranked: the pool's first n (`first`)");
    let s = |i: usize| (i == 5 || i == 7).then_some((0, 0)); // stragglers at indices 5 and 7, equally ranked
    assert_eq!(kept_indices(9, 3, 2, &s), vec![0, 1, 2, 5, 7], "stragglers first, in order");
    assert_eq!(kept_indices(9, 3, 3, &s), vec![0, 1, 2, 3, 5, 7], "the shortfall is the first other pool law");
    assert_eq!(kept_indices(9, 3, 0, &s), vec![0, 1, 2], "keep 0 reads no extra");
    assert_eq!(kept_indices(9, 3, 6, &s), (0..9).collect::<Vec<_>>(), "keep exactly the pool keeps the pool");
    assert_eq!(kept_indices(9, 3, 99, &s), (0..9).collect::<Vec<_>>(), "keep past the pool keeps the pool");
    assert_eq!(kept_indices(4, 9, 2, &none), vec![0, 1, 2, 3], "from past the end: all served, no pool");
    // a rank orders the stragglers, smallest first; equal ranks keep the stream order
    let c = |i: usize| [None, None, None, None, Some((0, 9)), Some((0, 2)), None, Some((0, 2)), Some((0, 5))][i];
    assert_eq!(kept_indices(9, 3, 2, &c), vec![0, 1, 2, 5, 7], "the two cheapest, the tie in stream order");
    assert_eq!(kept_indices(9, 3, 3, &c), vec![0, 1, 2, 5, 7, 8], "the third cheapest (rank (0, 5))");
    assert_eq!(kept_indices(9, 3, 5, &c), vec![0, 1, 2, 3, 4, 5, 7, 8], "a shortfall fills with the first other pool law, as for a constant rank");
    // the miner's rank is (steps, normal-form size): under an empty base every step count is 0 and the size decides
    let r = |i: usize| [None, None, None, Some((0, 30)), Some((0, 8)), Some((0, 20)), Some((2, 4))][i];
    assert_eq!(kept_indices(7, 3, 2, &r), vec![0, 1, 2, 4, 5], "equal steps: the smaller normal forms");
    assert_eq!(kept_indices(7, 3, 3, &r), vec![0, 1, 2, 3, 4, 5], "steps come first: the dearer small term waits");
    assert_eq!(Keep::parse("first"), Ok(Keep::First));
    assert_eq!(Keep::parse("small"), Ok(Keep::Small));
    assert!(Keep::parse("bogus").unwrap_err().contains("EXTRAS_SELECT"));
}

/// The served laws of `ROLLBACK_LAWS` with the pool `[clean, straggler]` after them (a law `and` commutes away; the
/// straggler is the first of the served file's own).
fn served_and_pool() -> (usize, String, String, String) {
    let named = |s: &str| {
        let (a, b) = s.split_once(" = ").unwrap();
        (s.to_string(), parse_term(a), parse_term(b))
    };
    let served: Vec<_> = ROLLBACK_LAWS.lines().map(named).collect();
    let job = &mut Job::new(Setup::process());
    let strag: String = tatic_kernel::scoped(|| {
        let out = classify(job, &served, UNBOUNDED, true, false);
        out.iter().zip(&served).find(|(o, _)| matches!(o, Outcome::Straggler(..))).expect("a straggler among the served laws").1 .0.clone()
    });
    (served.len(), ROLLBACK_LAWS.to_string(), "and(x, y) = and(y, x)".to_string(), strag)
}


/// The names of the stragglers `laws_for` leaves a mine with (a whole mine is too slow to run per case).
fn straggler_names(text: &str, extras: Option<ExtrasKeep>) -> Vec<String> {
    let named = |s: &str| {
        let (a, b) = s.split_once(" = ").unwrap();
        (s.to_string(), parse_term(a), parse_term(b))
    };
    let laws: Vec<_> = text.lines().map(named).collect();
    let env = vec![("RULEMINER_LAWFILE".to_string(), "unused".to_string()), ("RULEMINER_FAST".to_string(), "1".to_string()), ("RULEMINER_GUARD".to_string(), "0".to_string())];
    let setup = Setup::with_env(env);
    let job = &mut Job::new(setup.clone());
    let clock = Clock(std::cell::Cell::new(Instant::now()));
    let mut cfg = MinerConfig::new(&setup);
    cfg.extras = extras;
    tatic_kernel::scoped(|| laws_for(job, laws, &cfg, UNBOUNDED, &clock, false).stragglers.iter().map(|s| s.0.clone()).collect())
}

/// `small` keeps the pool's straggler over its clean law that comes first; `first` keeps the clean law and is today's
/// mine (the pool's cost is not paid); `KEEP=0` and a `FROM` past the end are the served laws alone and the whole file.
#[test]
fn the_pool_is_cut_by_the_stragglers_verdict() {
    let (from, served, clean, strag) = served_and_pool();
    let both = format!("{served}{clean}\n{strag}\n");
    let ex = |n, by| Some(ExtrasKeep { from, n, by });
    let base = straggler_names(&served, None);
    let by_straggler = straggler_names(&both, ex(1, Keep::Small));
    assert_eq!(by_straggler.len(), base.len() + 1, "the pool's straggler joins the served stragglers");
    assert_eq!(by_straggler.last(), Some(&strag));
    assert_eq!(straggler_names(&both, ex(1, Keep::First)), base, "the first pool law is the clean one: no new straggler");
    assert_eq!(straggler_names(&both, ex(0, Keep::Small)), base, "keep 0 reads no extra");
    assert_eq!(straggler_names(&both, Some(ExtrasKeep { from: 1000, n: 1, by: Keep::Small })), straggler_names(&both, None), "from past the end is the whole file as served");
}

/// `by=first` is today's mine rule for rule: a file with a pool and `KEEP` of the first law chooses what the file without the
/// pool does.
#[test]
fn extras_by_first_mines_what_the_unpooled_file_mines() {
    let (from, served, clean, strag) = served_and_pool();
    let mine_rules = |tag: &str, laws: &str, env: &[(&str, String)]| {
        let path = std::env::temp_dir().join(format!("extras_laws_{}_{tag}.txt", std::process::id()));
        std::fs::write(&path, laws).unwrap();
        let mut e = vec![("RULEMINER_LAWFILE".to_string(), path.display().to_string()), ("RULEMINER_FAST".to_string(), "1".to_string())];
        e.extend(env.iter().map(|(k, v)| (k.to_string(), v.clone())));
        let chosen = mine(&Setup::with_env(e), &[]).0;
        std::fs::remove_file(&path).ok();
        chosen
    };
    let pooled = mine_rules(
        "pooled",
        &format!("{served}{clean}\n{strag}\n"),
        &[("RULEMINER_EXTRAS_FROM", from.to_string()), ("RULEMINER_EXTRAS_KEEP", "1".to_string()), ("RULEMINER_EXTRAS_BY", "first".to_string())],
    );
    assert_eq!(pooled, mine_rules("plain", &format!("{served}{clean}\n"), &[]));
}

/// The three `RULEMINER_EXTRAS_*` variables become the config the mine keeps by (the `by_first` test above cannot tell
/// whether they were read: a mine that ignored them might choose the same rules), and none of them is no config.
#[test]
fn the_extras_env_becomes_the_config() {
    let cfg = |vars: &[(&str, &str)]| MinerConfig::new(&Setup::with_env(vars.iter().chain(&[("RULEMINER_LAWFILE", "unused")]).map(|(k, v)| (k.to_string(), v.to_string())).collect())).extras;
    assert!(cfg(&[]).is_none());
    let k = cfg(&[("RULEMINER_EXTRAS_FROM", "7"), ("RULEMINER_EXTRAS_KEEP", "3"), ("RULEMINER_EXTRAS_BY", "small")]).expect("set");
    assert_eq!((k.from, k.n, k.by), (7, 3, Keep::Small));
    let k = cfg(&[("RULEMINER_EXTRAS_FROM", "0"), ("RULEMINER_EXTRAS_KEEP", "5"), ("RULEMINER_EXTRAS_BY", "first")]).expect("set");
    assert_eq!((k.from, k.n, k.by), (0, 5, Keep::First));
}

/// `FROM` without `KEEP` and `BY` fails loudly, not as a half-set config.
#[test]
#[should_panic(expected = "RULEMINER_EXTRAS_KEEP")]
fn an_incomplete_extras_env_panics() {
    MinerConfig::new(&Setup::with_env(vec![("RULEMINER_LAWFILE".to_string(), "unused".to_string()), ("RULEMINER_EXTRAS_FROM".to_string(), "2".to_string())]));
}

/// A bad `BY`, `FROM` or `KEEP` value fails loudly and names its variable.
#[test]
fn a_bad_extras_env_value_names_its_variable() {
    let panic_of = |vars: [(&str, &str); 3]| {
        let vars: Vec<(String, String)> = vars.iter().chain(&[("RULEMINER_LAWFILE", "unused")]).map(|(k, v)| (k.to_string(), v.to_string())).collect();
        let Err(err) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| MinerConfig::new(&Setup::with_env(vars)))) else { panic!("a bad value must panic") };
        err.downcast_ref::<String>().cloned().unwrap_or_default()
    };
    assert!(panic_of([("RULEMINER_EXTRAS_FROM", "2"), ("RULEMINER_EXTRAS_KEEP", "3"), ("RULEMINER_EXTRAS_BY", "cheap")]).contains("RULEMINER_EXTRAS_BY"));
    assert!(panic_of([("RULEMINER_EXTRAS_FROM", "x"), ("RULEMINER_EXTRAS_KEEP", "3"), ("RULEMINER_EXTRAS_BY", "small")]).contains("RULEMINER_EXTRAS_FROM=x"));
    assert!(panic_of([("RULEMINER_EXTRAS_FROM", "2"), ("RULEMINER_EXTRAS_KEEP", "-1"), ("RULEMINER_EXTRAS_BY", "small")]).contains("RULEMINER_EXTRAS_KEEP=-1"));
}

/// A worker that panics fails the thread waiting for its result instead of hanging it: the waiter keeps a sender, so the
/// channel never closes (a band-17 mine hung at 0 CPU after a join step panicked, run `2026-10-25-held-seen`).
#[test]
fn a_panicked_worker_fails_its_waiter() {
    let (end_tx, end_rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let waited = std::panic::catch_unwind(|| {
            std::thread::scope(|sc| {
                let (tx, rx) = std::sync::mpsc::channel();
                for i in 0..2usize {
                    let tx = tx.clone();
                    sc.spawn(move || relay(|| if i == 1 { panic!("worker {i}") } else { i }, |r| drop(tx.send(r))));
                }
                rx.iter().take(2).map(|r: Result<usize, WorkerPanicked>| r.expect("a worker panicked")).sum::<usize>()
            })
        });
        let _ = end_tx.send(waited.is_err());
    });
    assert_eq!(end_rx.recv_timeout(std::time::Duration::from_secs(30)), Ok(true), "the waiter panics, not hangs");
}

/// Laws of a stream mine (the first of `2026-10-23-cold-streams`' phase-3 mine 1) for `a_false_winner_rolls_the_rounds_back`.
const ROLLBACK_LAWS: &str = "\
add(and(x, add(z, -1)), and(y, add(x, -1))) = add(and(y, add(x, -1)), and(x, add(z, -1)))
xor(shr1(-1, 0), xor(y, xor(z, -1))) = xor(xor(z, -1), xor(y, shr1(xor(x, xor(-1, x)), 0)))
sub(x, sub(z, shr1(sub(shr1(-1, 0), y), 0))) = sub(shr1(sub(shr1(-1, 0), y), 0), sub(z, x))
sub(y, xor(z, sub(x, shr1(x, 0)))) = sub(y, xor(z, sub(x, shr1(xor(sub(0, -1), x), 0))))
and(add(x, and(x, z)), add(x, and(y, z))) = and(add(x, and(z, y)), add(x, and(x, and(z, x))))
xor(x, xor(-1, and(xor(y, z), xor(x, y)))) = xor(xor(-1, y), and(xor(x, y), xor(x, z)))
xor(-1, or(xor(and(x, y), y), xor(x, z))) = xor(x, xor(-1, and(or(z, y), or(xor(y, x), z))))
or(y, or(z, sub(or(or(x, z), y), -1))) = or(or(z, y), sub(or(y, or(z, x)), -1))
add(sub(x, -1), xor(z, add(y, xor(x, z)))) = sub(x, xor(z, sub(xor(x, xor(-1, z)), y)))
add(add(y, z), and(add(x, x), add(x, y))) = add(y, add(z, and(shl1(x, 0), add(x, y))))
xor(x, xor(xor(-1, y), shl1(xor(x, xor(y, z)), 0))) = xor(xor(-1, x), xor(y, shl1(xor(xor(x, z), y), 0)))
sub(sub(z, x), sub(y, shl1(shl1(-1, 0), 0))) = sub(sub(z, y), sub(x, shl1(shl1(-1, 0), 0)))
sub(0, xor(y, sub(xor(x, y), xor(y, z)))) = sub(xor(sub(-1, y), sub(xor(x, y), xor(z, y))), -1)
or(or(x, y), shr1(or(x, or(y, z)), 0)) = or(x, or(y, or(shr1(or(z, y), 0), shr1(x, 0))))
and(xor(y, and(z, y)), shr1(and(x, y), 0)) = and(xor(y, z), and(y, xor(z, shr1(and(y, x), 0))))
and(sub(z, x), shr1(and(y, z), 0)) = and(shr1(y, 0), and(sub(z, x), shr1(z, 0)))
and(and(x, shr1(z, 0)), and(y, shl1(shl1(-1, 0), 0))) = and(shr1(z, 0), and(and(y, x), shl1(shl1(-1, 0), 0)))
or(add(y, add(add(x, -1), x)), add(y, or(y, z))) = or(add(y, or(y, z)), add(add(x, x), add(y, -1)))
add(xor(x, z), add(y, add(-1, and(x, y)))) = add(y, add(-1, add(and(x, y), xor(x, z))))
sub(sub(-1, z), add(x, add(x, add(x, y)))) = sub(0, add(x, add(add(x, x), add(z, sub(y, -1)))))
sub(sub(z, x), add(-1, or(add(-1, y), sub(x, y)))) = sub(z, add(x, add(-1, or(add(y, -1), sub(x, y)))))
and(and(x, y), xor(z, sub(y, xor(xor(x, y), -1)))) = and(x, and(y, xor(z, sub(y, sub(-1, xor(y, x))))))
and(add(add(z, z), -1), add(x, and(y, z))) = and(add(x, and(z, and(y, z))), add(z, add(z, -1)))
xor(x, xor(y, shl1(xor(x, xor(-1, z)), 0))) = xor(xor(y, x), shl1(xor(z, xor(-1, x)), 0))
";

/// A winner whose proof fails rolls the rounds back to its round, and the mine plays on without it (`Rounds::settle`):
/// offered a false but attractive candidate, a `RULEMINER_FAST` mine picks it, rolls back and ends where it would have
/// without it. Replaces `RULEMINER_EXTRA` and `docs/runs/2026-10-12/scripts/spec_rollback.sh` (CU4a).
#[test]
fn a_false_winner_rolls_the_rounds_back() {
    let path = std::env::temp_dir().join(format!("rollback_laws_{}.txt", std::process::id()));
    std::fs::write(&path, ROLLBACK_LAWS).unwrap();
    let setup = Setup::with_env(vec![("RULEMINER_LAWFILE".into(), path.display().to_string()), ("RULEMINER_FAST".into(), "1".into())]);
    let r = |l: &str, rhs: &str| (parse_term(l), parse_term(rhs));
    // it collapses every `sub`, so laws whose sides differ only inside one become `0 = 0`: it wins round 0
    let false_rule = r("sub(x, y)", "0");
    let (plain, plain_failed) = mine(&setup, &[]);
    let (chosen, failed) = mine(&setup, &[false_rule]);
    std::fs::remove_file(&path).ok();
    assert_eq!((plain_failed, failed), (0, 1), "the false rule won a round and failed its proof");
    // the rounds after the rollback replay the plain mine's (the false rule's left side has no candidate of its own here)
    assert_eq!(chosen, plain);
}

fn plan(vars: &[(&str, &str)]) -> Result<ExtrasPlan, String> {
    ExtrasPlan::from_vars(&Setup::with_env(vars.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect()), 319)
}

/// `POOL` and `EXTRAS_SELECT`: unset is today's draw (319 laws a mine); `first` and `small` pick the miner's selection;
/// anything else, a pool of more than one without a selector, or a pool of 0 is an error
/// naming the variables.
#[test]
fn the_extras_plan_parses_and_needs_a_selector_for_a_pool() {
    let p = plan(&[]).unwrap();
    assert_eq!((p.n, p.pool, p.by, p.per_mine()), (319, 1, None, 319));
    let p = plan(&[("EXTRAS_N", "5"), ("POOL", "4"), ("EXTRAS_SELECT", "first")]).unwrap();
    assert_eq!((p.n, p.pool, p.by, p.per_mine()), (5, 4, Some(Keep::First), 20));
    assert_eq!(plan(&[("EXTRAS_SELECT", "small")]).unwrap().by, Some(Keep::Small));
    assert!(plan(&[("EXTRAS_SELECT", "bogus")]).unwrap_err().contains("EXTRAS_SELECT"));
    assert!(plan(&[("POOL", "4")]).unwrap_err().contains("EXTRAS_SELECT"));
    assert!(plan(&[("POOL", "0")]).unwrap_err().contains("POOL"));
}

/// What `child_env` writes, `MinerConfig::new` reads back as the same extras (the driver and the miner
/// agree on the three `RULEMINER_EXTRAS_*` variables).
#[test]
fn the_extras_plan_round_trips_through_the_miner_config() {
    for select in ["first", "small"] {
        let vars = vec![("EXTRAS_N", "7"), ("POOL", "3"), ("EXTRAS_SELECT", select)];
        let p = plan(&vars).unwrap();
        let mut env = p.child_env(11);
        env.push(("RULEMINER_LAWFILE".to_string(), "unused".to_string()));
        let c = MinerConfig::new(&Setup::with_env(env));
        let k = c.extras.expect("set");
        assert_eq!((k.from, k.n, Some(k.by)), (11, 7, p.by), "{select}");
    }
}
