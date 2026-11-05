use super::*;

fn p(a: &str, b: &str) -> (Term, Term) {
    (parse_term(a), parse_term(b))
}

fn pl(a: &str, b: &str, straggler: bool, steps: i64, uncovered: bool) -> PoolLaw {
    PoolLaw { law: p(a, b), straggler, steps, size: steps, fallbacks: steps as u64, uncovered }
}

#[test]
fn pool_tsv_has_one_line_per_law_and_empty_cells_for_clean_laws() {
    let rows = vec![(0, "add(x, y) = add(y, x)".to_string(), Some((3, 7, 2)), true), (1, "and(x, y) = and(y, x)".to_string(), None, false)];
    let text = pool_tsv(&rows);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines, vec!["0\tadd(x, y) = add(y, x)\t1\t3\t7\t2\t1", "1\tand(x, y) = and(y, x)\t0\t\t\t\t0"]);
}

#[test]
fn read_pool_inverts_pool_tsv() {
    let rows = vec![(0, "add(x, y) = add(y, x)".to_string(), Some((3, 7, 2)), true), (1, "and(x, y) = and(y, x)".to_string(), None, false), (2, "or(x, y) = or(y, x)".to_string(), Some((1, 4, 1)), false)];
    let pool = read_pool(&pool_tsv(&rows));
    assert_eq!(pool.len(), 3);
    assert!(pool[0].straggler && pool[0].uncovered && (pool[0].steps, pool[0].size, pool[0].fallbacks) == (3, 7, 2));
    assert!(!pool[1].straggler && !pool[1].uncovered);
    assert!(pool[2].straggler && !pool[2].uncovered);
    assert!(pool[1].law == p("and(x, y)", "and(y, x)"));
}

#[test]
fn percentiles_share_the_average_rank_for_ties() {
    assert_eq!(percentiles(&[1.0, 2.0, 2.0, 3.0]), vec![0.0, 0.5, 0.5, 1.0]);
    assert_eq!(percentiles(&[3.0, 1.0]), vec![1.0, 0.0]);
}

#[test]
fn percentiles_of_one_value_is_half() {
    assert_eq!(percentiles(&[7.0]), vec![0.5]);
    assert!(percentiles(&[]).is_empty());
}

#[test]
fn group1_is_zero_for_non_stragglers_and_in_unit_range() {
    let pool = vec![pl("add(x, y)", "add(y, x)", true, 3, true), pl("and(x, y)", "and(y, x)", false, 9, false), pl("or(x, y)", "or(y, x)", true, 8, false)];
    let g = group1(&pool);
    assert_eq!(g[1], [0.0; 3]);
    assert_eq!((g[0], g[2]), ([0.0; 3], [1.0; 3]));
    assert!(g.iter().flatten().all(|v| (0.0..=1.0).contains(v)));
}

#[test]
fn group2_identical_operator_multiset_gives_jaccard_one() {
    let pool = vec![pl("add(x, y)", "add(y, x)", true, 1, true)];
    let g = group2(&pool, &[p("add(x, y)", "add(y, x)")]);
    assert_eq!(g[0], [1.0, 1.0, 1.0, 1.0]);
}

#[test]
fn group2_with_no_served_stragglers_is_zero_not_nan() {
    let pool = vec![pl("add(x, y)", "add(y, x)", true, 1, true)];
    assert_eq!(group2(&pool, &[])[0], [0.0; 4]);
    // a law that is all leaves has no operator and matches nothing
    let leaf = vec![pl("x", "x", true, 1, true)];
    assert_eq!(group2(&leaf, &[p("add(x, y)", "add(y, x)")])[0], [0.0; 4]);
}

#[test]
fn group3_is_zero_for_clean_laws_and_the_uncovered_fraction_otherwise() {
    let pool = vec![
        pl("add(x, y)", "add(y, x)", true, 1, true),
        pl("add(x, 0)", "x", true, 2, false),
        pl("and(x, y)", "and(y, x)", false, 0, false),
        pl("and(x, x)", "x", true, 3, true),
    ];
    let g = group3(&pool);
    assert_eq!(g[0], [1.0, 0.5]); // one of the two `add` stragglers stays uncovered
    assert_eq!(g[1], [0.0, 0.5]);
    assert_eq!(g[2], [0.0, 0.0]);
    assert_eq!(g[3], [1.0, 1.0]);
}

#[test]
fn rows_are_deterministic_35_wide_and_finite() {
    let pool = vec![pl("add(x, y)", "add(y, x)", true, 1, true), pl("and(x, y)", "and(y, x)", false, 0, false)];
    let served = [p("sub(x, y)", "sub(y, x)")];
    let (a, b) = (rows(&pool, &served), rows(&pool, &served));
    assert_eq!(a, b);
    assert!(a.iter().all(|r| r.len() == WIDTH && WIDTH == 35 && r.iter().all(|v| v.is_finite())));
}

#[test]
fn a_pool_with_no_stragglers_gives_finite_columns() {
    let pool = vec![pl("and(x, y)", "and(y, x)", false, 0, false)];
    let r = rows(&pool, &[]);
    assert!(r[0].iter().all(|v| v.is_finite()));
    assert_eq!(&r[0][PER_LAW..], &[0.0; 9]);
}

#[test]
fn auc_of_known_scores() {
    assert_eq!(auc(&[(0.1, false), (0.4, false), (0.35, true), (0.8, true)]), 0.75);
    assert_eq!(auc(&[(1.0, true), (1.0, false)]), 0.5, "a tie counts half");
    assert_eq!(auc(&[(1.0, true), (2.0, true)]), 0.5, "no negatives: no information");
    assert_eq!(auc(&[(1.0, true), (1.0, false), (2.0, true), (0.0, false)]), 0.875);
}

#[test]
#[should_panic(expected = "fit needs rows")]
fn fit_refuses_no_rows() {
    fit(&[]);
}

#[test]
fn per_law_features_are_symmetric_finite_and_26_long() {
    let (l, r) = (p("add(x, y)", "add(y, x)"), p("add(y, x)", "add(x, y)"));
    assert_eq!(per_law_features(&l), per_law_features(&r));
    assert!(per_law_features(&(Term::ZERO, Term::ONES)).iter().all(|f| f.is_finite()), "a law with no variables");
    assert_eq!(per_law_features(&l).len(), 26);
}

#[test]
fn model_text_round_trips_and_refuses_a_wrong_layout() {
    let rows: Vec<(Vec<f32>, bool)> = (0..20).map(|i| (vec![1.0, i as f32, (i % 3) as f32], i > 9)).collect();
    let m = fit(&rows);
    assert_eq!(Model::from_text(&m.to_text("v1"), "v1").unwrap(), m);
    assert!(Model::from_text(&m.to_text("v1"), "v2").is_err());
    assert!(Model::from_text("layout v1\nwidth 3", "v1").is_err(), "a garbled file is an error that says so");
    assert!(Model::from_text("", "v1").is_err());
}

#[test]
fn fit_separates_a_separable_set_and_repeats_bit_for_bit() {
    let rows: Vec<(Vec<f32>, bool)> = (1..=10).map(|i| (vec![1.0, i as f32], i > 5)).collect();
    let (a, b) = (fit(&rows), fit(&rows));
    assert_eq!(a, b);
    assert_eq!(auc(&rows.iter().map(|(f, y)| (a.score(f), *y)).collect::<Vec<_>>()), 1.0);
}

#[test]
fn a_constant_column_is_omitted_and_scores_finite() {
    let rows: Vec<(Vec<f32>, bool)> = (0..10).map(|i| (vec![1.0, 7.0, i as f32], i > 4)).collect();
    let m = fit(&rows);
    assert_eq!(m.dropped(), vec![1]);
    assert!(m.score(&[1.0, 7.0, 3.0]).is_finite());
}

#[test]
fn labels_credit_covered_stragglers_only() {
    let extras = "add(x, y) = add(y, x)\nand(x, y) = and(y, x)\nor(x, y) = or(y, x)\n";
    let log = "RULEMINER 2 stragglers of 9 laws, 1.0s base (0 unproved)\n\
               RULEMINER label: 1 add(x, y) = add(y, x)\n\
               RULEMINER label: 0 and(x, y) = and(y, x)\n\
               RULEMINER label: 1 some(other, law) = served\n";
    let rows = mine_labels(extras, log, "label").unwrap();
    assert_eq!(rows, vec![("add(x, y) = add(y, x)".to_string(), true), ("and(x, y) = and(y, x)".to_string(), false), ("or(x, y) = or(y, x)".to_string(), false)]);
}

#[test]
fn a_log_with_stragglers_and_no_label_lines_is_refused() {
    let old = "RULEMINER 5 stragglers of 9 laws, 1.0s base (0 unproved)\nRULEMINER uncovered: x\n";
    assert!(mine_labels("add(x, y) = add(y, x)\n", old, "label").is_err());
    let none = "RULEMINER 0 stragglers of 9 laws, 1.0s base (0 unproved)\n";
    assert_eq!(mine_labels("add(x, y) = add(y, x)\n", none, "label").unwrap(), vec![("add(x, y) = add(y, x)".to_string(), false)]);
    assert!(mine_labels("add(x, y) = add(y, x)\n", "RULEMINER something else\n", "label").is_err());
}

#[test]
fn the_salt_is_the_arm_folders_number() {
    assert_eq!(salt_of("C:/runs/2026-11-01-v06-dump/s7_A/cold_streams_streams_1_none"), Some(7));
    assert_eq!(salt_of("C:/runs/state/none"), None);
    assert_eq!(salt_of("C:\\runs\\s7_A\\x"), Some(7), "backslash paths");
    assert_eq!(salt_of("C:/runs/s3_old/s9_B/x"), Some(9), "the folder nearest the file wins");
}

#[test]
fn capture_at_k_counts_positives_in_the_top_k() {
    let (order, y) = ([2, 0, 1, 3], [true, false, true, false]);
    assert_eq!(capture_at_k(&order, &y, 2), 2);
    assert_eq!(capture_at_k(&order, &y, 1), 1);
    assert_eq!(capture_at_k(&order, &y, 0), 0);
    assert_eq!(capture_at_k(&order, &y, 99), 2, "k past the order counts the whole order");
    assert_eq!(capture_at_k(&[3, 1], &y, 2), 0, "only the ordered laws count");
}

#[test]
fn random_capture_of_all_positives_is_k() {
    assert_eq!(random_capture(&[true; 10], 4, 1..=200), 4.0);
    assert_eq!(random_capture(&[true; 10], 20, 1..=200), 10.0, "k past the laws counts them all");
    assert_eq!(random_capture(&[false; 10], 4, 1..=200), 0.0);
    let one = random_capture(&[true, false, false, false], 2, 1..=200);
    assert!((one - 0.5).abs() < 0.1, "one positive in four, top two: {one}");
}

#[test]
fn small_order_matches_kept_indices_semantics() {
    let st = |steps: i64, size: i64| PoolLaw { law: p("x", "x"), straggler: true, steps, size, fallbacks: 0, uncovered: false };
    let clean = || PoolLaw { law: p("x", "x"), straggler: false, steps: 0, size: 0, fallbacks: 0, uncovered: false };
    let pool = vec![clean(), st(2, 5), clean(), st(0, 9), st(2, 3), clean()];
    assert_eq!(small_order(&pool, 6), vec![3, 4, 1, 0, 2, 5], "stragglers by (steps, size), then the rest in stream order");
    assert_eq!(small_order(&pool, 4), vec![3, 1, 0, 2], "a slice reads only its first laws");
    let rank = |i: usize| pool[i].straggler.then_some((pool[i].steps, pool[i].size));
    for m in 0..=6 {
        let mut top = small_order(&pool, 6)[..m].to_vec();
        top.sort_unstable();
        assert_eq!(top, super::super::miner::kept_indices(6, 0, m, &rank), "the first {m}");
    }
}

#[test]
fn bootstrap_interval_of_a_constant_positive_sample_excludes_zero() {
    let (lo, hi) = bootstrap_interval(&[3.0; 42], 2000, 7);
    assert!(lo > 0.0 && lo == 3.0 && hi == 3.0, "{lo} {hi}");
    let signs: Vec<f64> = (0..42).map(|i| if i % 2 == 0 { 1.0 } else { -1.0 }).collect();
    let (lo, hi) = bootstrap_interval(&signs, 2000, 7);
    assert!(lo < 0.0 && hi > 0.0, "a mean of zero straddles it: {lo} {hi}");
}

#[test]
fn bootstrap_is_deterministic_for_a_seed() {
    let xs: Vec<f64> = (0..42).map(|i| (i * 37 % 11) as f64 - 3.0).collect();
    assert_eq!(bootstrap_interval(&xs, 2000, 7), bootstrap_interval(&xs, 2000, 7));
    assert_ne!(bootstrap_interval(&xs, 2000, 7), bootstrap_interval(&xs, 2000, 8));
}

#[test]
fn the_gate_needs_both_intervals_and_five_salts() {
    assert!(gate_ok((0.1, 0.3), (0.2, 0.5), 5));
    assert!(!gate_ok((0.0, 0.3), (0.2, 0.5), 7), "d's interval touches zero");
    assert!(!gate_ok((0.1, 0.3), (-0.1, 0.5), 7), "e's interval straddles zero");
    assert!(!gate_ok((0.1, 0.3), (0.2, 0.5), 4), "four salts of seven");
}

#[test]
fn loo_split_never_shares_a_salt() {
    let s = loo_split(&[5, 4, 6, 4]);
    assert_eq!(s, vec![(4, vec![5, 6]), (5, vec![4, 6]), (6, vec![4, 5])], "sorted, repeats collapsed");
    assert!(s.iter().all(|(held, train)| !train.contains(held)));
}

const FIVE: [&str; 5] = ["add(x, y) = add(y, x)", "and(x, y) = and(y, x)", "or(x, y) = or(y, x)", "xor(x, y) = xor(y, x)", "add(x, 0) = x"];

/// Writes one mine under `root/s<salt>_A/cold_streams_streams_1_none/`: a pool dump whose first law is a straggler, the
/// `laws_extra` file `extras`, one served law and a log crediting the pool's first law.
fn write_mine(root: &std::path::Path, salt: usize, m: &str, pool: &[&str], extras: &[&str]) {
    let d = root.join(format!("s{salt}_A")).join("cold_streams_streams_1_none");
    std::fs::create_dir_all(&d).unwrap();
    let tsv: String = pool.iter().enumerate().map(|(i, l)| if i == 0 { format!("{i}\t{l}\t1\t2\t9\t0\t0\n") } else { format!("{i}\t{l}\t0\t\t\t\t0\n") }).collect();
    std::fs::write(d.join(format!("dump_{m}_pool.tsv")), tsv).unwrap();
    std::fs::write(d.join(format!("dump_{m}_served.txt")), "sub(y, 0) = y\n").unwrap();
    std::fs::write(d.join(format!("laws_extra_{m}.txt")), extras.join("\n") + "\n").unwrap();
    std::fs::write(d.join(format!("mine_{m}.log")), format!("RULEMINER 1 stragglers of 9 laws, 0.0s base (0 unproved)\nRULEMINER label: 1 {}\n", pool[0])).unwrap();
}

fn scratch(tag: &str) -> std::path::PathBuf {
    let root = std::env::temp_dir().join(format!("ctx_scorer_{tag}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    root
}

#[test]
fn load_mines_drops_later_duplicates_and_counts_them() {
    let root = scratch("dup");
    write_mine(&root, 4, "0", &FIVE, &FIVE);
    let b = [FIVE[2], FIVE[1], FIVE[3], FIVE[0], FIVE[4]]; // its first two laws repeat salt 4's
    write_mine(&root, 5, "0", &b, &b);
    let (mines, dropped) = load_mines(&[&root.join("s4_A"), &root.join("s5_A")], 3).unwrap();
    assert_eq!((mines.len(), dropped), (2, 2));
    assert_eq!(mines[0].live, vec![true, true, true]);
    assert_eq!(mines[1].live, vec![false, false, true], "the first occurrence (salt 4) stays, later copies go");
    assert_eq!((mines[0].salt, mines[1].salt, mines[0].y.len(), mines[0].pool.len(), mines[0].served.len()), (4, 5, 3, 5, 1));
    assert_eq!(mines[0].y, vec![true, false, false], "the log credits the pool's first law");
}

#[test]
fn load_mines_stops_when_the_first_n_pool_laws_do_not_match_laws_extra() {
    let root = scratch("mismatch");
    let swapped = [FIVE[1], FIVE[0], FIVE[2], FIVE[3], FIVE[4]];
    write_mine(&root, 4, "0", &FIVE, &swapped);
    let err = load_mines(&[&root.join("s4_A")], 3).err().expect("a refusal");
    assert!(err.contains("laws_extra"), "{err}");
}

#[test]
fn load_mines_stops_on_a_repeat_inside_one_mines_own_file() {
    let root = scratch("repeat");
    let twice = [FIVE[0], FIVE[1], FIVE[0], FIVE[3], FIVE[4]];
    write_mine(&root, 4, "0", &twice, &twice);
    let err = load_mines(&[&root.join("s4_A")], 3).err().expect("a refusal");
    assert!(err.contains("repeat"), "{err}");
}

#[test]
fn load_mines_stops_when_a_credited_law_is_no_straggler() {
    let root = scratch("credit");
    write_mine(&root, 4, "0", &FIVE, &FIVE);
    let log = root.join("s4_A/cold_streams_streams_1_none/mine_0.log");
    std::fs::write(&log, format!("RULEMINER 1 stragglers of 9 laws, 0.0s base (0 unproved)\nRULEMINER label: 1 {}\n", FIVE[1])).unwrap();
    let err = load_mines(&[&root.join("s4_A")], 3).err().expect("a refusal");
    assert!(err.contains("straggler"), "{err}");
}

/// A mine of 20 pool laws (the first 15 labelled) built from `seed` alone.
fn synthetic(salt: usize, seed: usize) -> Mine {
    let nest = |op: &str, d: usize| (0..d).fold("x".to_string(), |s, _| format!("{op}({s}, y)"));
    let pool: Vec<PoolLaw> = (0..20)
        .map(|i| {
            let j = i + seed;
            PoolLaw { law: p(&nest("add", j % 5 + 1), &nest("and", j % 3 + 1)), straggler: j % 3 != 0, steps: (j % 7) as i64, size: (j % 11) as i64, fallbacks: (j % 2) as u64, uncovered: j % 4 == 0 }
        })
        .collect();
    let y: Vec<bool> = (0..15).map(|i| pool[i].straggler && (i + seed) % 4 < 2).collect();
    Mine { salt, pool, served: vec![p("add(x, y)", "add(y, x)")], y, live: vec![true; 15] }
}

fn fixture_mines() -> Vec<Mine> {
    (4..=10).flat_map(|s| (0..2).map(move |m| synthetic(s, s * 2 + m))).collect()
}

#[test]
fn q1_header_names_the_context_variant() {
    let mines = fixture_mines();
    let full = q1(&mines, &[3], "context");
    assert!(full.starts_with("context model: context (35 columns)\n"), "{full}");
    let no_g3 = q1(&mines, &[3], NO_G3);
    assert!(no_g3.starts_with("context model: drop group 3 (33 columns)\n"), "{no_g3}");
}

#[test]
fn q1_context_report_apart_from_the_header_equals_the_old_report() {
    let full = q1(&fixture_mines(), &[3, 6], "context");
    let rest = full.split_once('\n').unwrap().1;
    assert_eq!(rest, GOLDEN_Q1);
}

#[test]
fn q1_swapped_context_keeps_every_variant_in_the_ablation() {
    let t = q1(&fixture_mines(), &[3], NO_G3);
    for name in ["context ", "per-law ", "drop group 1 ", "drop group 2 ", "drop group 3 ", "drop per-law "] {
        assert!(t.contains(&format!("{name}")), "{name}: {t}");
    }
}

#[test]
#[should_panic(expected = "bogus")]
fn q1_refuses_an_unknown_variant() {
    q1(&fixture_mines(), &[3], "bogus");
}

#[test]
fn runtime_rows_equal_rows_projected_on_runtime_cols() {
    for (salt, seed) in [(4, 3), (5, 8)] {
        let m = synthetic(salt, seed);
        let (full, rt) = (rows(&m.pool, &m.served), runtime_rows(&m.pool, &m.served));
        assert_eq!(rt.len(), full.len());
        for i in 0..full.len() {
            assert_eq!(rt[i], project(&full[i], &runtime_cols()), "pool law {i}");
        }
    }
}

#[test]
fn runtime_cols_has_33_columns_and_no_group3() {
    let cols = runtime_cols();
    assert_eq!(cols.len(), WIDTH - 2);
    assert!(cols.contains(&0) && cols.iter().all(|&c| c < WIDTH - 2));
    assert_eq!(variants().iter().find(|(n, _)| *n == NO_G3).unwrap().1, cols);
}

#[test]
fn ctx_ranks_orders_stragglers_by_score_and_leaves_the_rest_none() {
    let r = ctx_ranks(&[0.1, 5.0, 3.0, 9.0], &[true, true, false, true]);
    assert_eq!(r, vec![Some(2), Some(1), None, Some(0)]);
}

#[test]
fn ctx_ranks_of_equal_scores_is_stream_order() {
    let r = ctx_ranks(&[1.0, 1.0, 1.0, 1.0], &[true, false, true, true]);
    assert_eq!(r, vec![Some(0), None, Some(1), Some(2)]);
}

#[test]
fn ctx_ranks_survives_nan() {
    let r = ctx_ranks(&[f64::NAN, 1.0, f64::NAN, 2.0], &[true; 4]);
    let mut got: Vec<i64> = r.iter().map(|x| x.unwrap()).collect();
    got.sort_unstable();
    assert_eq!(got, vec![0, 1, 2, 3], "distinct ranks");
}

fn salted_mines() -> Vec<Mine> {
    (4..=6).flat_map(|s| (0..2).map(move |m| synthetic(s, s * 2 + m))).collect()
}

#[test]
fn fit_model_uses_only_the_named_salts_and_width_is_the_runtime_width() {
    let mines = salted_mines();
    let mut train = vec![];
    for m in mines.iter().filter(|m| m.salt == 5) {
        let rt = runtime_rows(&m.pool, &m.served);
        train.extend((0..m.y.len()).filter(|&i| m.live[i] && m.pool[i].straggler).map(|i| (rt[i].clone(), m.y[i])));
    }
    let model = fit_model(&mines, &[5]);
    assert_eq!(model, fit(&train));
    assert_eq!(model.width(), WIDTH - 2);
    assert_ne!(model, fit_model(&mines, &[4, 6]));
}

#[test]
#[should_panic(expected = "salts")]
fn fit_model_refuses_salts_with_no_rows() {
    fit_model(&salted_mines(), &[99]);
}

#[test]
fn parse_salts_reads_ranges_and_lists() {
    assert_eq!(parse_salts("4-10"), (4..=10).collect::<Vec<_>>());
    assert_eq!(parse_salts("7"), vec![7]);
    assert_eq!(parse_salts("1,3"), vec![1, 3]);
}

#[test]
fn overlap_counts_shared_law_texts_in_the_train_slice_only() {
    let root = scratch("overlap");
    write_mine(&root, 4, "0", &FIVE, &FIVE);
    write_mine(&root, 1, "0", &["or(x, y) = or(y, x)", "mul(x, y) = mul(y, x)"], &["or(x, y) = or(y, x)", "mul(x, y) = mul(y, x)"]);
    // train slice 2: FIVE[0], FIVE[1] count; FIVE[2] ("or") is past the slice, so the shared "or" law is not counted
    assert_eq!(overlap(&[&root.join("s4_A")], 2, &[&root.join("s1_A")]), (0, 2));
    // slice 3 reaches FIVE[2]: one of the two eval texts is in the train slice
    assert_eq!(overlap(&[&root.join("s4_A")], 3, &[&root.join("s1_A")]), (1, 2));
}

const GOLDEN_Q1: &str = r#"Q1 14 mines, 7 salts, slice 15 laws; live stragglers 140, credited 69
salt 4: 2 mines, 20 live stragglers, 9 credited
salt 5: 2 mines, 20 live stragglers, 9 credited
salt 6: 2 mines, 20 live stragglers, 10 credited
salt 7: 2 mines, 20 live stragglers, 11 credited
salt 8: 2 mines, 20 live stragglers, 11 credited
salt 9: 2 mines, 20 live stragglers, 10 credited
salt 10: 2 mines, 20 live stragglers, 9 credited
held-out AUC (mean over salts): context 0.9209, per-law 0.7605
k=3: ceiling 42; capture sums: context 42, per-law 36, small 15, random 14.0, random stragglers-first 20.7
k=3: d (context - per-law) mean 0.429, 95% [0.143, 0.786]; salts above 0: 3/7
k=3: e (context - small) mean 1.929, 95% [1.500, 2.357]; salts above 0: 7/7
k=3: per-salt d [0.0, 0.0, 0.0, 0.0, 1.0, 2.0, 3.0], e [5.0, 6.0, 6.0, 3.0, 2.0, 2.0, 3.0]; salts with both above 0: 3/7; gate not met
k=3: ablation capture sums: context 42, per-law 36, drop group 1 42, drop group 2 38, drop group 3 38, drop per-law 39
k=6: ceiling 69; capture sums: context 58, per-law 47, small 40, random 27.8, random stragglers-first 41.4
k=6: d (context - per-law) mean 0.786, 95% [0.429, 1.143]; salts above 0: 5/7
k=6: e (context - small) mean 1.286, 95% [1.071, 1.571]; salts above 0: 7/7
k=6: per-salt d [1.0, 0.0, 0.0, 2.0, 2.0, 2.0, 4.0], e [2.0, 3.0, 2.0, 3.0, 2.0, 2.0, 4.0]; salts with both above 0: 5/7; gate met
k=6: ablation capture sums: context 58, per-law 47, drop group 1 58, drop group 2 56, drop group 3 55, drop per-law 62
gate met at k in [6]; no room at k in []
verdict FAIL
"#;

#[test]
fn q1_is_deterministic_and_reports_both_ks_and_a_verdict() {
    let mines: Vec<Mine> = (4..=10).flat_map(|s| (0..2).map(move |m| synthetic(s, s * 2 + m))).collect();
    let (a, b) = (q1(&mines, &[3, 6], "context"), q1(&mines, &[3, 6], "context"));
    assert_eq!(a, b);
    assert!(a.contains("k=3") && a.contains("k=6") && a.contains("verdict"), "{}", a);
    assert!(a.contains("drop group 1") && a.contains("drop per-law"), "{}", a);
}
