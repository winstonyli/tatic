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
    straggler_names_dumping(text, extras, None)
}

/// `straggler_names` with the pool dump to `prefix` (`RULEMINER_POOL_DUMP`).
fn straggler_names_dumping(text: &str, extras: Option<ExtrasKeep>, prefix: Option<String>) -> Vec<String> {
    straggler_names_with(text, extras, prefix, None)
}

/// `straggler_names_dumping` with the context model's weights file (`RULEMINER_CTX_WEIGHTS`).
fn straggler_names_with(text: &str, extras: Option<ExtrasKeep>, prefix: Option<String>, weights: Option<&str>) -> Vec<String> {
    let named = |s: &str| {
        let (a, b) = s.split_once(" = ").unwrap();
        (s.to_string(), parse_term(a), parse_term(b))
    };
    let laws: Vec<_> = text.lines().map(named).collect();
    let mut env = vec![("RULEMINER_LAWFILE".to_string(), "unused".to_string()), ("RULEMINER_FAST".to_string(), "1".to_string()), ("RULEMINER_GUARD".to_string(), "0".to_string())];
    env.extend(weights.map(|w| ("RULEMINER_CTX_WEIGHTS".to_string(), w.to_string())));
    let setup = Setup::with_env(env);
    let job = &mut Job::new(setup.clone());
    let clock = Clock(std::cell::Cell::new(Instant::now()));
    let mut cfg = MinerConfig::new(&setup);
    (cfg.extras, cfg.pool_dump) = (extras, prefix);
    tatic_kernel::scoped(|| laws_for(job, laws, &cfg, &[], UNBOUNDED, &clock, false).stragglers.iter().map(|s| s.0.clone()).collect())
}

/// The pool dump of a `first` mine writes one line per pool law with its facts and the served stragglers' normal forms, and
/// the mine reads the laws it would without it.
#[test]
fn the_pool_dump_writes_facts_and_changes_nothing() {
    let (from, served, clean, strag) = served_and_pool();
    let both = format!("{served}{clean}\n{strag}\n");
    let ex = Some(ExtrasKeep { from, n: 1, by: Keep::First });
    let prefix = std::env::temp_dir().join(format!("pool_dump_{}", std::process::id())).display().to_string();
    let without = straggler_names(&both, ex);
    let with = straggler_names_dumping(&both, ex, Some(prefix.clone()));
    let (pool_file, served_file) = (format!("{prefix}_pool.tsv"), format!("{prefix}_served.txt"));
    let (pool, forms) = (std::fs::read_to_string(&pool_file).unwrap(), std::fs::read_to_string(&served_file).unwrap());
    std::fs::remove_file(&pool_file).ok();
    std::fs::remove_file(&served_file).ok();
    assert_eq!(with, without, "the dump changes no law the mine reads");
    let pool = crate::ctx_scorer::read_pool(&pool);
    assert_eq!(pool.len(), 2, "one line per pool law, not per kept law");
    assert!(!pool[0].straggler && !pool[0].uncovered, "the clean law is no straggler");
    assert!(pool[1].straggler && pool[1].steps >= 0 && pool[1].size > 0 && pool[1].fallbacks > 0);
    assert_eq!(forms.lines().count(), straggler_names(&served, None).len(), "one normal form per served straggler");
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

/// A one-column context model (`ctx33-v1` layout, 33 wide): score = `w` times column `col`.
fn one_column_model(col: usize, w: i32) -> String {
    format!("layout ctx33-v1\nwidth 33\nkeep {col}\nmean 0\nscale 1\nw {w}\n")
}

/// The all-zero model: every law scores 0.
fn zero_model() -> String {
    "layout ctx33-v1\nwidth 33\nkeep 0\nmean 0\nscale 1\nw 0\n".to_string()
}

/// `text` written to a fresh weights file (named by `tag` and this process); the path.
fn weights_file(tag: &str, text: &str) -> String {
    let path = std::env::temp_dir().join(format!("ctx_weights_{tag}_{}.txt", std::process::id()));
    std::fs::write(&path, text).unwrap();
    path.display().to_string()
}

/// The stragglers `laws_for` leaves under `EXTRAS_BY=ctx` with the model `model`, then the weights file removed.
fn ctx_names(text: &str, extras: ExtrasKeep, tag: &str, model: &str) -> Vec<String> {
    let path = weights_file(tag, model);
    let names = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| straggler_names_with(text, Some(extras), None, Some(&path))));
    std::fs::remove_file(&path).ok();
    names.unwrap_or_else(|e| std::panic::resume_unwind(e))
}

/// The pool of `ROLLBACK_LAWS` after its first two laws (the served ones): per pool law its name, whether it is a straggler
/// and its `runtime_rows` (what the context model scores).
fn rollback_pool() -> (usize, Vec<String>, Vec<bool>, Vec<Vec<f32>>) {
    let named: Vec<(String, Term, Term)> = ROLLBACK_LAWS
        .lines()
        .map(|s| {
            let (a, b) = s.split_once(" = ").unwrap();
            (s.to_string(), parse_term(a), parse_term(b))
        })
        .collect();
    let from = 2;
    let job = &mut Job::new(Setup::with_env(vec![("RULEMINER_FAST".to_string(), "1".to_string())]));
    let rows = tatic_kernel::scoped(|| {
        let outcomes = classify(job, &named, UNBOUNDED, true, false);
        let (pool, served) = pool_laws(&named, &outcomes, from);
        (pool.iter().map(|p| p.straggler).collect::<Vec<_>>(), crate::ctx_scorer::runtime_rows(&pool, &served))
    });
    (from, named[from..].iter().map(|n| n.0.clone()).collect(), rows.0, rows.1)
}

#[test]
fn keep_parses_ctx_and_names_the_variable_on_error() {
    assert_eq!(Keep::parse("ctx"), Ok(Keep::Ctx));
    assert!(Keep::parse("bogus").unwrap_err().contains("ctx"), "the error lists the choices");
}

/// A zero model scores every law alike, so ranks fall back to the stream order and `ctx` keeps what `small` keeps when the
/// pool holds one straggler.
#[test]
fn a_ctx_pool_with_a_zero_model_keeps_the_straggler_like_small() {
    let (from, served, clean, strag) = served_and_pool();
    let both = format!("{served}{clean}\n{strag}\n");
    let ex = |by| ExtrasKeep { from, n: 1, by };
    let by_ctx = ctx_names(&both, ex(Keep::Ctx), "zero", &zero_model());
    assert_eq!(by_ctx, straggler_names(&both, Some(ex(Keep::Small))));
    assert_eq!(by_ctx.last(), Some(&strag), "the pool's straggler is kept over the clean law before it");
}

#[test]
#[should_panic(expected = "RULEMINER_CTX_WEIGHTS")]
fn ctx_without_weights_names_the_variable() {
    let (from, served, clean, strag) = served_and_pool();
    straggler_names_with(&format!("{served}{clean}\n{strag}\n"), Some(ExtrasKeep { from, n: 1, by: Keep::Ctx }), None, None);
}

#[test]
#[should_panic(expected = "RULEMINER_CTX_WEIGHTS")]
fn ctx_refuses_a_missing_weights_file() {
    let (from, served, clean, strag) = served_and_pool();
    let gone = std::env::temp_dir().join(format!("ctx_weights_gone_{}.txt", std::process::id())).display().to_string();
    straggler_names_with(&format!("{served}{clean}\n{strag}\n"), Some(ExtrasKeep { from, n: 1, by: Keep::Ctx }), None, Some(&gone));
}

#[test]
#[should_panic(expected = "layout")]
fn ctx_refuses_weights_of_another_layout() {
    let (from, served, clean, strag) = served_and_pool();
    ctx_names(&format!("{served}{clean}\n{strag}\n"), ExtrasKeep { from, n: 1, by: Keep::Ctx }, "layout", &zero_model().replace("ctx33-v1", "ctx35-v1"));
}

#[test]
#[should_panic(expected = "width")]
fn ctx_refuses_weights_of_another_width() {
    let (from, served, clean, strag) = served_and_pool();
    ctx_names(&format!("{served}{clean}\n{strag}\n"), ExtrasKeep { from, n: 1, by: Keep::Ctx }, "width", "layout ctx33-v1\nwidth 5\nkeep 0\nmean 0\nscale 1\nw 0\n");
}

#[test]
fn ctx_with_n_zero_reads_no_extra() {
    let (from, served, clean, strag) = served_and_pool();
    let both = format!("{served}{clean}\n{strag}\n");
    assert_eq!(ctx_names(&both, ExtrasKeep { from, n: 0, by: Keep::Ctx }, "n0", &zero_model()), straggler_names(&served, None));
}

/// The pool facts the ctx rank scores (`pool_laws` over `classify`) are the ones the dump wrote, which the model was fit on.
#[test]
fn ctx_pool_facts_equal_the_dump_rows() {
    let (from, text) = (2, ROLLBACK_LAWS);
    let prefix = std::env::temp_dir().join(format!("ctx_parity_{}", std::process::id())).display().to_string();
    straggler_names_dumping(text, Some(ExtrasKeep { from, n: 1, by: Keep::First }), Some(prefix.clone()));
    let (pool_file, served_file) = (format!("{prefix}_pool.tsv"), format!("{prefix}_served.txt"));
    let (tsv, forms) = (std::fs::read_to_string(&pool_file).unwrap(), std::fs::read_to_string(&served_file).unwrap());
    std::fs::remove_file(&pool_file).ok();
    std::fs::remove_file(&served_file).ok();
    let named: Vec<(String, Term, Term)> = text
        .lines()
        .map(|s| {
            let (a, b) = s.split_once(" = ").unwrap();
            (s.to_string(), parse_term(a), parse_term(b))
        })
        .collect();
    let job = &mut Job::new(Setup::with_env(vec![("RULEMINER_FAST".to_string(), "1".to_string())]));
    let (dumped, live) = tatic_kernel::scoped(|| {
        let dumped = crate::ctx_scorer::read_pool(&tsv);
        let dumped_served: Vec<(Term, Term)> = forms.lines().map(|l| l.split_once(" = ").map(|(a, b)| (parse_term(a), parse_term(b))).unwrap()).collect();
        let outcomes = classify(job, &named, UNBOUNDED, true, false);
        let (pool, served) = pool_laws(&named, &outcomes, from);
        let facts = |p: &[crate::ctx_scorer::PoolLaw]| p.iter().map(|l| (l.straggler, l.steps, l.size, l.fallbacks)).collect::<Vec<_>>();
        ((facts(&dumped), crate::ctx_scorer::runtime_rows(&dumped, &dumped_served)), (facts(&pool), crate::ctx_scorer::runtime_rows(&pool, &served)))
    });
    assert!(live.0.iter().any(|f| f.0), "the fixture's pool has stragglers");
    assert_eq!(live, dumped);
}

/// `ctx` keeps the pool straggler the model scores highest, not the one with the fewest steps: a one-column model of either
/// sign keeps the straggler with that column's extreme value, and the two signs keep different laws.
#[test]
fn ctx_follows_the_model_not_the_steps() {
    let (from, names, straggler, rows) = rollback_pool();
    assert!(straggler.iter().filter(|&&s| s).count() >= 3, "the fixture's pool needs several stragglers to order");
    let ex = ExtrasKeep { from, n: 1, by: Keep::Ctx };
    let text = ROLLBACK_LAWS;
    let pick = |col: usize, up: bool| {
        let ss: Vec<usize> = (0..names.len()).filter(|&i| straggler[i]).collect();
        // first of the extreme: equal scores keep the stream order
        ss.iter().copied().fold(ss[0], |best, i| if (up && rows[i][col] > rows[best][col]) || (!up && rows[i][col] < rows[best][col]) { i } else { best })
    };
    let col = (1..crate::ctx_scorer::PER_LAW).find(|&c| pick(c, true) != pick(c, false)).expect("some per-law column separates the pool's stragglers");
    let (up, down) = (ctx_names(text, ex, "up", &one_column_model(col, 1)), ctx_names(text, ex, "down", &one_column_model(col, -1)));
    assert_eq!(up.last(), Some(&names[pick(col, true)]), "a positive weight keeps the highest column value (from offset {from})");
    assert_eq!(down.last(), Some(&names[pick(col, false)]), "a negative weight keeps the lowest");
}

#[test]
fn ctx_reports_how_many_kept_differ_from_small() {
    assert_eq!(kept_differ(&[0, 1, 4, 6], &[0, 1, 5, 6], 2), 1);
    assert_eq!(kept_differ(&[0, 1, 4, 6], &[0, 1, 4, 6], 2), 0);
    assert_eq!(kept_differ(&[0, 1], &[0, 1], 5), 0, "no pool laws kept");
}

/// What a quiet `cover` of the stream mine's laws (`ROLLBACK_LAWS`) under `setup` does: how many rules it chose and, per law
/// (as plain values, the kernel scope lets no terms out), whether it is a straggler under the base (by `classify` and by
/// `still_stragglers` with nothing chosen) and with the chosen rules.
struct QuietCover {
    chosen: usize,
    by_classify: Vec<bool>,
    none: Vec<bool>,
    with: Vec<bool>,
}

fn quiet_cover(setup: &Arc<Setup>) -> QuietCover {
    let laws: Vec<(String, Term, Term)> = ROLLBACK_LAWS
        .lines()
        .map(|s| {
            let (a, b) = s.split_once(" = ").unwrap();
            (s.to_string(), parse_term(a), parse_term(b))
        })
        .collect();
    let job = &mut Job::new(setup.clone());
    let clock = Clock(std::cell::Cell::new(Instant::now()));
    let (chosen, by_classify, none, with) = tatic_kernel::scoped(|| {
        let cfg = MinerConfig::new(setup);
        let l = laws_of(job, laws.clone(), 0, true, UNBOUNDED, &clock, false);
        let chosen = cover(job, &l, &cfg, &[], &clock, &[], true).0;
        let by_classify: Vec<bool> = classify(job, &laws, UNBOUNDED, true, false).iter().map(|o| matches!(o, Outcome::Straggler(..))).collect();
        let (none, with) = (still_stragglers(job, &[], &[], &laws, UNBOUNDED, true), still_stragglers(job, &[], &chosen, &laws, UNBOUNDED, true));
        (chosen.len(), by_classify, none, with)
    });
    QuietCover { chosen, by_classify, none, with }
}

fn fast_env(file: &std::path::Path) -> Vec<(String, String)> {
    vec![("RULEMINER_LAWFILE".to_string(), "unused".to_string()), ("RULEMINER_FAST".to_string(), "1".to_string()), ("CTX_TEST_RESULTS".to_string(), file.display().to_string())]
}

/// With nothing chosen the pool's stragglers are the base's; a rule the quiet cover chose closes at least one of them.
#[test]
fn a_chosen_rule_flips_a_straggler_to_covered() {
    let setup = Setup::with_env(fast_env(std::path::Path::new("unused")));
    let QuietCover { chosen, by_classify, none, with } = quiet_cover(&setup);
    assert!(chosen > 0, "the stream mine's laws leave a rule to choose");
    assert_eq!(none, by_classify, "no chosen rules is the base classification");
    let (a, b) = (none.iter().filter(|s| **s).count(), with.iter().filter(|s| **s).count());
    assert!(a > 0 && b < a, "the chosen rules close a straggler: {a} -> {b}");
    assert!(with.iter().zip(&none).all(|(w, n)| !w || *n), "a clean law stays clean");
}

/// A quiet cover leaves no `chosen` record in the setup's result file.
#[test]
fn a_quiet_cover_records_no_chosen_rule() {
    let file = std::env::temp_dir().join(format!("quiet_cover_{}.tsv", std::process::id()));
    let setup = Setup::for_task(fast_env(&file), std::fs::File::create(&file).unwrap());
    let chosen = quiet_cover(&setup).chosen;
    let recorded = std::fs::read_to_string(&file).unwrap();
    std::fs::remove_file(&file).ok();
    assert!(chosen > 0);
    assert!(!recorded.contains("chosen"), "a quiet cover records nothing: {recorded:?}");
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
