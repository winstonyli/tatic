use super::rewrite::Node;
use super::*;

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

/// Rewriting with the library rules over every constant-multiplication law (search note section 35): per law the
/// carries of the target machines, whether a whole-term machine proof was still needed, build and check times; the
/// totals show what the rules buy. `ABLATE=shldist,shldistsub,double,doublechain` (any subset) removes rules.
#[test]
#[ignore]
pub fn rewrite_rules_over_the_mul_laws() {
    tatic::kernel::scoped(|| {
        let _banner = MachineBanner::start("RULES");
        let max = env_or("MULMINER_MAX", 7);
        let (mut proved, mut none, mut machine_free, mut over_cap, t0) = (0, 0, 0, 0, Instant::now());
        for (name, t1, t2) in mul_laws(max) {
            if !t1.is_law(&t2, 2) {
                continue;
            }
            let cs = [&t1, &t2].map(|t| Machine::parse(t).map_or(0, |m| m.carries()));
            let before = MACHINE_FALLBACKS.with(|c| c.get());
            let t = Instant::now();
            let r = rewrite_law(4, 2, &t1, &t2);
            let built = t.elapsed();
            let fell = MACHINE_FALLBACKS.with(|c| c.get()) - before;
            match r {
                Some((p, s)) => {
                    let t = Instant::now();
                    ck(&name, &p, &s);
                    proved += 1;
                    machine_free += (fell == 0) as u32;
                    over_cap += (cs[0].max(cs[1]) > carry_cap()) as u32;
                    println!("RULES {name}: carries {cs:?}, machine proofs used {fell}, build {built:?}, check {:?}", t.elapsed());
                }
                None => {
                    none += 1;
                    println!("RULES {name}: carries {cs:?}, no proof, {built:?}");
                }
            }
        }
        println!("RULES {proved} proved ({machine_free} with no whole-term machine proof, {over_cap} beyond the carry cap), {none} not, {:?}", t0.elapsed());
    })
}

/// Rules from a file, one `lhs -> rhs` per line in `Term::show` syntax (blank lines and `#` comments skipped); the format of `RULEMINER_EXTRA`.
pub fn read_rule_file(path: &str) -> Vec<(Term, Term)> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let mut out = vec![];
    let mut seen = hashbrown::HashSet::new();
    for line in text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        let Some((l, r)) = line.split_once(" -> ") else {
            println!("RULEMINER extra file: skipped (no ' -> '): {line}");
            continue;
        };
        let parsed = std::panic::catch_unwind(|| (parse_term(l.trim()), parse_term(r.trim())));
        match parsed {
            Ok((l, r)) if matches!(*l.node(), Node::Op(..)) && l != r && seen.insert((l, r)) => out.push((l, r)),
            Ok(_) => {}
            Err(_) => println!("RULEMINER extra file: skipped (unparsable): {line}"),
        }
    }
    out
}

/// The candidate laws of a miner family (`mul`, `shl`, `lt`, `shr`; the `RULEMINER_*` env vars size them).
/// `laws` reordered by a hash of the salt and each law's text (FNV-1a: deterministic across runs); salt 0 keeps the order.
pub fn shuffled(mut laws: Vec<(Term, Term)>, salt: usize) -> Vec<(Term, Term)> {
    if salt != 0 {
        laws.sort_by_cached_key(|(a, b)| format!("{salt}|{} = {}", a.show(), b.show()).bytes().fold(0xcbf29ce484222325u64, |h, c| (h ^ c as u64).wrapping_mul(0x100000001b3)));
    }
    laws
}

/// `RULEMINER_SHUFFLE`: a permutation of the sorted sequence, fixed per salt, different between salts, and the batches of a shuffled
/// stream differ from the lexicographic ones.
#[test]
pub fn shuffle_is_a_fixed_permutation() {
    let laws = |salt: usize, take: usize| {
        let env = move |k: &str, d: usize| match k {
            "RULEMINER_SHUFFLE" => salt,
            "RULEMINER_LAWS" => take,
            "RULEMINER_STRIDE" => 1,
            "RULEMINER_DEEP3" => 1,
            _ => d,
        };
        family_laws("add3", &env, 4, 3, 7).into_iter().map(|(name, _, _)| name).collect::<Vec<_>>()
    };
    let (sorted, a, a2, b) = (laws(0, 100000), laws(1, 100000), laws(1, 100000), laws(2, 100000));
    assert_eq!(a, a2, "same salt, same order");
    assert_ne!(a, sorted);
    assert_ne!(a, b);
    let set = |v: &Vec<String>| v.iter().cloned().collect::<std::collections::BTreeSet<_>>();
    assert!(set(&a) == set(&sorted) && set(&b) == set(&sorted) && a.len() == sorted.len(), "a permutation");
    let first_char = |v: &[String]| v.iter().take(50).map(|s| s.chars().next().unwrap()).collect::<std::collections::BTreeSet<_>>();
    println!("first 50 laws, leading characters: sorted {:?}, shuffled {:?}", first_char(&sorted), first_char(&a));
}

/// `u3w` interleaves its three families in equal parts: a window of 30 laws holds 10 comparison laws (cmp3d), and its stride and
/// phase windows are subsequences of the same sequence.
#[test]
pub fn u3w_window_is_an_equal_mix() {
    let laws = |stride: usize, phase: usize| {
        let env = move |k: &str, d: usize| match k {
            "RULEMINER_LAWS" => 30,
            "RULEMINER_STRIDE" => stride,
            "RULEMINER_PHASE" => phase,
            _ => d,
        };
        family_laws("u3w", &env, 4, 3, 7).into_iter().map(|(name, _, _)| name).collect::<Vec<_>>()
    };
    let w = laws(1, 0);
    assert_eq!(w.len(), 30);
    assert_eq!(w.iter().filter(|s| s.contains("lt(")).count(), 10);
    assert_eq!(laws(3, 1)[..5], w[1..].iter().step_by(3).take(5).cloned().collect::<Vec<_>>()[..]);
}

pub fn family_laws(family: &str, env: &dyn Fn(&str, usize) -> usize, n: usize, nv: usize, max: u32) -> Vec<(String, Term, Term)> {
    if family == "u3w" {
        // u3 with equal shares: the add3, sbo3 and cmp3d sequences (each shuffled as `RULEMINER_SHUFFLE` says) interleaved round-robin,
        // so a window holds the three families in equal parts instead of in proportion to their sizes (cmp3d has 4x add3's laws)
        let whole = |f: &str| {
            let e = |k: &str, d: usize| match k {
                "RULEMINER_STRIDE" => 1,
                "RULEMINER_PHASE" | "RULEMINER_SKIP" => 0,
                "RULEMINER_LAWS" => usize::MAX,
                _ => env(k, d),
            };
            family_laws(f, &e, n, nv, max).into_iter()
        };
        let mut seqs: Vec<_> = ["add3", "sbo3", "cmp3d"].iter().map(|f| whole(f)).collect();
        let mut mixed = Vec::new();
        loop {
            let before = mixed.len();
            mixed.extend(seqs.iter_mut().filter_map(|s| s.next()));
            if mixed.len() == before {
                break;
            }
        }
        mixed.into_iter().skip(env("RULEMINER_PHASE", 0)).step_by(env("RULEMINER_STRIDE", 1)).skip(env("RULEMINER_SKIP", 0)).take(env("RULEMINER_LAWS", 250)).collect()
    } else if family == "shl" {
        let conj = shl_conjectures(2);
        let stride = (conj.len() / env("RULEMINER_LAWS", 250)).max(1);
        conj.into_iter().step_by(stride).map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b)).collect()
    } else if family == "shr" {
        // right shifts of the arithmetic pool terms, against every term of the pool and its right shifts
        // RULEMINER_DEEP=1: the depth-2 pool of `terms` (set `MINER_SUB=1` to include `sub`)
        let pool = if env("RULEMINER_DEEP", 0) == 1 { terms(2, true).to_vec() } else { lt_pool(2) };
        let shr = |a: &Term| Term::op(SHR1, *a, Term::ZERO);
        let all: Vec<Term> = pool.iter().cloned().chain(pool.iter().map(&shr)).collect();
        pool_conjectures(all, n, nv, 0)
            .into_iter()
            .filter(|(a, b)| a.has_shift() || b.has_shift())
            .step_by(env("RULEMINER_STRIDE", 1))
            .take(env("RULEMINER_LAWS", 250))
            .map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b))
            .collect()
    } else if let Some(seq) = pool3_sequence(family, env, n) {
        seq.iter()
            .filter(|(a, b)| env("RULEMINER_SHAPE", 2) == 2 || shape_part(a, b) == env("RULEMINER_SHAPE", 2)) // `RULEMINER_SHAPE=0|1`: one of two structure-based halves
            .skip(env("RULEMINER_PHASE", 0)) // with a stride, the phase picks the residue class: phases 0..stride tile the sequence
            .step_by(env("RULEMINER_STRIDE", 1))
            .skip(env("RULEMINER_SKIP", 0))
            .take(env("RULEMINER_LAWS", 250))
            .map(|(a, b)| (format!("{} = {}", a.show(), b.show()), *a, *b))
            .collect()
    } else if family == "lt" {
        let pool = lt_pool(2);
        let all = pool.iter().flat_map(|a| pool.iter().map(move |b| Term::op(LT, *a, *b)));
        pool_conjectures(all, n, nv, env("RULEMINER_LAWS", 250)).into_iter().map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b)).collect()
    } else {
        mul_laws(max)
    }
}

/// A three-variable family's law sequence: its pool's (`pool3`) conjectures that use all three variables, shuffled by
/// `RULEMINER_SHUFFLE=<salt>` (0 = off; a hash of each law, so a window of it, a batch or a stride phase, samples the whole family
/// instead of one lexicographic range). Built once per process for each family, `RULEMINER_DEEP3`, width and salt: the driver
/// takes every child's law window from it (`driver::write_laws`), where each child used to rebuild the pool (35% of a sweep's
/// loops) and the driver to clone and reshuffle it per child (6% of a sweep, docs/tier-cycle.md).
fn pool3_sequence(family: &str, env: &dyn Fn(&str, usize) -> usize, n: usize) -> Option<std::sync::Arc<Vec<(Term, Term)>>> {
    // keyed by every variable it reads; `None` (not a pool3 family) is kept too
    static MEMO: crate::task::SharedMemo<(String, usize, usize, usize), Option<std::sync::Arc<Vec<(Term, Term)>>>> = crate::task::SharedMemo::new();
    let salt = env("RULEMINER_SHUFFLE", 0);
    let build = || {
        let mut seq = shuffled(pool_conjectures(pool3(family, env)?, n, 3, 0), salt);
        seq.retain(|(a, b)| (0..3).all(|v| a.has_var(v) || b.has_var(v)));
        Some(std::sync::Arc::new(seq))
    };
    MEMO.with((family.to_string(), env("RULEMINER_DEEP3", 0), n, salt), build, |c| c.clone())
}

/// A law window written as a law file (`driver::write_laws`) and read back (`read_laws`) gives the same laws, names included.
#[test]
pub fn law_windows_survive_a_law_file() {
    let env = |k: &str, d: usize| match k {
        "RULEMINER_SKIP" => 40,
        "RULEMINER_LAWS" => 60,
        "RULEMINER_SHUFFLE" => 1,
        "RULEMINER_DEEP3" => 1,
        _ => d,
    };
    for family in ["add3", "cmp3d"] {
        let laws = family_laws(family, &env, 4, 3, 7);
        assert_eq!(laws.len(), 60);
        let path = std::env::temp_dir().join(format!("law_window_{family}_{}.txt", std::process::id()));
        std::fs::write(&path, laws_text(&laws)).unwrap();
        let back = read_named_laws(path.to_str().unwrap());
        std::fs::remove_file(&path).unwrap();
        assert!(back == laws, "{family}");
    }
}

/// Laws as the `lhs = rhs` lines `read_laws` reads.
pub fn laws_text(laws: &[(String, Term, Term)]) -> String {
    laws.iter().map(|(_, a, b)| format!("{} = {}\n", a.show(), b.show())).collect()
}

/// `RULEMINER_SKIP` windows: consecutive windows tile the law sequence, and a window past the end is empty.
#[test]
pub fn family_law_windows_tile_the_sequence() {
    let laws = |skip: usize, take: usize| {
        let env = move |k: &str, d: usize| match k {
            "RULEMINER_SKIP" => skip,
            "RULEMINER_LAWS" => take,
            "RULEMINER_STRIDE" => 1,
            _ => d,
        };
        family_laws("add3", &env, 4, 3, 7).into_iter().map(|(name, _, _)| name).collect::<Vec<_>>()
    };
    let whole = laws(0, 12);
    assert_eq!(whole.len(), 12);
    let mut tiled = laws(0, 5);
    tiled.extend(laws(5, 7));
    assert_eq!(tiled, whole);
    assert!(laws(usize::MAX / 2, 5).is_empty());
}

/// Which of two halves a law belongs to, by the shape of its two sides with variables erased (constants and operators kept):
/// laws that differ only in which variables appear share a half, so near-variants never straddle a split.
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

pub fn shape_part(a: &Term, b: &Term) -> usize {
    shape_part_salted(a, b, &env_var("RULEMINER_SHAPE_SALT").unwrap_or_default()) // a different salt gives a different split; unset keeps the original halves
}

fn shape_part_salted(a: &Term, b: &Term, salt: &str) -> usize {
    fn skeleton(t: &Term, out: &mut String) {
        match *t.node() {
            Node::V(_) => out.push('v'),
            Node::Zero => out.push('0'),
            Node::Ones => out.push('1'),
            Node::Op(o, x, y) => {
                out.push_str(&format!("({o} "));
                skeleton(&x, out);
                out.push(' ');
                skeleton(&y, out);
                out.push(')');
            }
        }
    }
    let mut s = salt.to_string();
    skeleton(a, &mut s);
    s.push('=');
    skeleton(b, &mut s);
    // FNV-1a: deterministic across runs and platforms
    let h = s.bytes().fold(0xcbf29ce484222325u64, |h, c| (h ^ c as u64).wrapping_mul(0x100000001b3));
    (h >> 32) as usize & 1
}

/// `RULEMINER_SHAPE`: the two shape halves are disjoint, together are the whole sequence, and renaming variables keeps a law in its half.
#[test]
pub fn family_law_shape_halves_partition() {
    for family in THREE_VAR_FAMILIES {
        shape_halves_partition(family);
    }
}

fn shape_halves_partition(family: &str) {
    let laws = |shape: usize| {
        let env = move |k: &str, d: usize| match k {
            "RULEMINER_SHAPE" => shape,
            "RULEMINER_LAWS" => 100000,
            "RULEMINER_STRIDE" => 1,
            "RULEMINER_DEEP3" => 1,
            _ => d,
        };
        family_laws(family, &env, 4, 3, 7).into_iter().map(|(name, _, _)| name).collect::<std::collections::BTreeSet<_>>()
    };
    let (whole, h0, h1) = (laws(2), laws(0), laws(1));
    println!("shape halves {family}: {} + {} = {}", h0.len(), h1.len(), whole.len());
    assert!(h0.is_disjoint(&h1) && h0.len() + h1.len() == whole.len(), "{} {} {}", h0.len(), h1.len(), whole.len());
    assert!(!h0.is_empty() && !h1.is_empty());
    let (x, y, z) = (parse_term("add(x, y)"), parse_term("add(y, z)"), parse_term("sub(x, z)"));
    assert_eq!(shape_part(&x, &z), shape_part(&y, &z));
}

/// A different salt re-splits the laws (so the split is not one fixed key), and each salt still keeps variable renamings together.
#[test]
pub fn shape_salt_changes_the_split() {
    let laws = ["add(x, y)", "sub(add(x, y), z)", "add(sub(x, y), z)", "sub(x, sub(y, z))", "add(x, sub(y, z))", "sub(xor(x, -1), y)", "add(shl1(x, 0), y)", "sub(add(x, y), xor(z, -1))"];
    let rhs = parse_term("sub(x, y)");
    let half = |salt: &str| laws.iter().map(|l| shape_part_salted(&parse_term(l), &rhs, salt)).collect::<Vec<_>>();
    assert_ne!(half(""), half("a"));
    for salt in ["", "a"] {
        assert_eq!(shape_part_salted(&parse_term("add(x, y)"), &rhs, salt), shape_part_salted(&parse_term("add(y, z)"), &rhs, salt));
    }
}

/// `RULEMINER_PHASE`: with stride 2 the two phases are disjoint and together are the stride-1 sequence.
#[test]
pub fn family_law_phases_are_disjoint() {
    let laws = |stride: usize, phase: usize, take: usize| {
        let env = move |k: &str, d: usize| match k {
            "RULEMINER_STRIDE" => stride,
            "RULEMINER_PHASE" => phase,
            "RULEMINER_LAWS" => take,
            _ => d,
        };
        family_laws("add3", &env, 4, 3, 7).into_iter().map(|(name, _, _)| name).collect::<Vec<_>>()
    };
    let (even, odd, whole) = (laws(2, 0, 6), laws(2, 1, 6), laws(1, 0, 12));
    assert_eq!(even.len() + odd.len(), 12);
    let woven: Vec<String> = even.iter().zip(&odd).flat_map(|(a, b)| [a.clone(), b.clone()]).collect();
    assert_eq!(woven, whole);
}

/// Every `RULEMINER_*` switch of `rule_miner`, read once (defaults in `from_env`), except the law window's (`RULEMINER_LAWS`,
/// `_SHAPE`, `_SHAPE_SALT`, `_PHASE`, `_STRIDE` and the like), which `family_laws` reads through the `env` it is given.
pub struct MinerConfig {
    /// `MULMINER_MAX`: largest constant in the mul family.
    pub max: u32,
    /// `RULEMINER_TRIALS`: candidate cap.
    pub trials: usize,
    /// `RULEMINER_PERM`: 0 strict rule order, 1 ties broken by `tie_greater`, 2 no order check.
    pub perm: usize,
    /// `RULEMINER_STEPS`: per-law rewrite budget once a base set is loaded.
    pub steps: usize,
    /// `RULEMINER_VARS`: variable cap of cross-side rules.
    pub vars: usize,
    /// `RULEMINER_ROUNDS`: greedy rounds (default no cap: the mine stops when no candidate gains; a cap trimmed general rules,
    /// docs/tier-cycle.md "cmp3d's library lost its general rules"; with `RULEMINER_SHOW=1`, 0 just lists the candidates).
    pub rounds: usize,
    /// `RULEMINER_THREADS`: scoring threads, clamped to 1..=12.
    pub threads: usize,
    /// `RULEMINER_ANY`, `_SHOW`, `_FAST`: switches (`env_flag`), off by default.
    pub any_op: bool,
    pub show: bool,
    pub fast: bool,
    /// `RULEMINER_FAMILY`: the law family (default `mul`); with `lawfile` it still sets the variable count.
    pub family: String,
    /// `RULEMINER_BASE=<file>`: rules (`lhs -> rhs` lines) and their preferences in force throughout (section 74).
    pub base: Option<String>,
    /// `RULEMINER_LAWFILE=<file>`: mine from these `lhs = rhs` lines (a proposer's band) instead of the family's window.
    pub lawfile: Option<String>,
    /// `RULEMINER_GUARD=<k>`: about k machine-free laws scored with the stragglers (default 120, 0 = off).
    pub guard: usize,
    /// `RULEMINER_EXTRA=<file>`: extra candidates (`lhs -> rhs` lines).
    pub extra: Option<String>,
    /// `RULEMINER_NODUPLHS` (switch, on by default): drop candidates whose left side already has a rule in `base`.
    pub no_dup_lhs: bool,
    /// `RULEMINER_PREFS` (switch, off by default): run the preference phase.
    pub prefs: bool,
    /// `RULEMINER_UNITS=<file>`: the base's drop units, read only with `prefs`.
    pub units: Option<String>,
}

impl MinerConfig {
    pub fn from_env() -> Self {
        let flag = |k: &str| env_flag(k, false);
        let path = |k: &str| env_var(k).map(String::from);
        MinerConfig {
            max: env_or("MULMINER_MAX", 7) as u32,
            trials: env_or("RULEMINER_TRIALS", 400),
            perm: env_or("RULEMINER_PERM", 0),
            steps: env_or("RULEMINER_STEPS", 200),
            vars: env_or("RULEMINER_VARS", 4),
            rounds: env_or("RULEMINER_ROUNDS", usize::MAX),
            threads: env_or("RULEMINER_THREADS", 1).clamp(1, 12),
            any_op: flag("RULEMINER_ANY"),
            show: flag("RULEMINER_SHOW"),
            fast: flag("RULEMINER_FAST"),
            family: env_var("RULEMINER_FAMILY").unwrap_or("mul").into(),
            base: path("RULEMINER_BASE"),
            lawfile: path("RULEMINER_LAWFILE"),
            guard: env_or("RULEMINER_GUARD", 120),
            extra: path("RULEMINER_EXTRA"),
            no_dup_lhs: env_flag("RULEMINER_NODUPLHS", true),
            prefs: flag("RULEMINER_PREFS"),
            units: path("RULEMINER_UNITS"),
        }
    }
}

/// Rule miner (search note section 36): candidate rules are the equal pairs of the `shl1` pool (two variables, width 4,
/// the shl miner's pool), oriented to a strictly smaller right side and proved by `add_tree_law`. The targets are the
/// mul laws that still needed a whole-term machine proof under the built-in rules (the "stragglers"). A candidate is
/// tried on the stragglers whose normalized terms contain an instance of its left side; it scores by the machine
/// proofs it removes. Env: `MULMINER_MAX` (default 7), `RULEMINER_TRIALS` (candidate cap, default 400).
#[test]
#[ignore]
pub fn rule_miner() {
    tatic::kernel::scoped(|| {
        // the join store this mine feeds from this thread (`JoinStore`); the scoring workers read a copy of it
        set_join_store(Some(JoinStoreUse::Feed(JoinStore::default())));
        // phase clock: `phase(label)` prints the seconds since the previous mark
        let last = std::cell::Cell::new(Instant::now());
        let phase = |label: &str| {
            println!("RULEMINER time {label}: {:.1}s", last.replace(Instant::now()).elapsed().as_secs_f64());
        };
        let _banner = MachineBanner::start("RULEMINER");
        let _save = lemma_cache::Save;
        let cfg = MinerConfig::from_env();
        let (max, trials) = (cfg.max, cfg.trials);
        // RULEMINER_PERM=1: ties in the rule order are broken by `tie_greater` (reassociation rules; section 70), 2: no order check; the step budget
        // and the same-term check in `rule_step` still back up termination, and soundness is unaffected
        let ok_order = |l: &Term, r: &Term| match cfg.perm {
            0 => rule_order_ok(l, r),
            1 => rule_order_or_tie(l, r),
            _ => true, // 2: no order check at all (the miner's own cross-side rules are not ordered either)
        };
        let family = cfg.family.as_str();
        // the stragglers are the laws left with the base's rules
        let base_text = cfg.base.as_ref().map(|f| std::fs::read_to_string(f).unwrap()).unwrap_or_default();
        let (base, base_prefs) = (parse_rules(&base_text), parse_prefs(&base_text));
        set_extra_rules(base.clone());
        set_rule_prefs(base_prefs.clone());
        // `add3` laws have three variables (the candidate generator below still builds patterns over at most two)
        let (n, nv, kv) = (4usize, 2usize, if family_vars(&family) == 3 { 3usize } else { 2 });
        let fallbacks = || MACHINE_FALLBACKS.with(|c| c.get());
        // stragglers under the built-in rules
        let mut stragglers: Vec<(String, Term, Term, [Term; 2], u64, std::time::Duration)> = vec![];
        // a lawfile is a proposer's band (docs/tier-cycle.md)
        let laws = match &cfg.lawfile {
            Some(f) => read_named_laws(f),
            None => family_laws(&family, &env_or::<usize>, n, nv, max),
        };
        phase("law building");
        let mut unproved = 0usize;
        let mut clean: Vec<(String, Term, Term)> = vec![]; // laws that are already machine-free under the base rules (for `RULEMINER_GUARD`)
        // `RULEMINER_FAST` counts the base rules' machine proofs the way it scores candidates: without building them
        SCORE_ONLY.with(|s| s.set(cfg.fast));
        for (name, t1, t2) in laws.iter().cloned() {
            if !t1.is_law(&t2, kv) || [&t1, &t2].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap())) {
                continue;
            }
            let before = fallbacks();
            let t = Instant::now();
            // base rules may loop; the step budget bounds them (the built-in rules never reach it)
            RULE_BUDGET.with(|b| b.set(if base.is_empty() { i64::MAX / 2 } else { cfg.steps as i64 }));
            let r = rewrite_plan(n, kv, &t1, &t2);
            let took = t.elapsed();
            let fell = fallbacks() - before;
            // a law the rewriter cannot close at all counts as a straggler too (fixed once it is proved machine-free)
            unproved += r.is_none() as usize;
            let fell = if r.is_none() { fell.max(1) } else { fell };
            if r.is_none() || fell > 0 {
                RULE_BUDGET.with(|b| b.set(if base.is_empty() { i64::MAX / 2 } else { cfg.steps as i64 }));
                let normal = [rewrite(&t1, n, kv).0, rewrite(&t2, n, kv).0];
                println!("RULEMINER straggler {name}: {} = {} ({fell} machine proofs, {took:?}{})", normal[0].show(), normal[1].show(), if r.is_none() { ", UNPROVED" } else { "" });
                stragglers.push((name, t1, t2, normal, fell, took));
            } else {
                clean.push((name, t1, t2));
            }
        }
        SCORE_ONLY.with(|s| s.set(false));
        let base_time: f64 = stragglers.iter().map(|s| s.5.as_secs_f64()).sum();
        println!("RULEMINER {family}: {} stragglers of {} laws, {:.1}s base ({unproved} unproved)", stragglers.len(), laws.len(), base_time);
        phase("laws and stragglers");
        // `RULEMINER_GUARD=<k>` (default 120, 0 = off): about k of the already machine-free laws are scored with the stragglers, so a candidate that breaks them loses
        // the same 1000 per law as it gains per straggler fixed (the miner otherwise sees only the stragglers and cannot see a regression)
        let guard_k = cfg.guard;
        let mut scored = stragglers.clone();
        let mut guard_w = 1000i64; // each sampled guard law stands for clean/sampled laws, so a regression costs that many times 1000
        if guard_k > 0 && !clean.is_empty() {
            let (step, w) = guard_plan(clean.len(), guard_k);
            guard_w = w;
            for (name, t1, t2) in clean.iter().step_by(step) {
                scored.push((name.clone(), *t1, *t2, [*t1, *t2], 1, std::time::Duration::ZERO));
            }
            println!("RULEMINER guard: {} machine-free laws scored of {} (weight {guard_w} each)", scored.len() - stragglers.len(), clean.len());
        }
        // goal-directed candidates: abstract each arithmetic subterm of a straggler's normalized terms into a pattern over
        // at most two variables (cutting subterms into variables), and look for a smaller term over the same variables
        // with the same values at width 4 (a pool of all terms up to 5 nodes, indexed by value)
        let psize = 5;
        let mut by_size: Vec<Vec<Term>> = vec![vec![]; psize + 1];
        by_size[1] = vec![Term::v(0), Term::v(1), Term::ZERO, Term::ONES];
        for sz in 2..=psize {
            let mut level = vec![];
            for x in &by_size[sz - 1] {
                level.push(Term::op(SHL1, *x, Term::ZERO));
                level.push(Term::op(SHR1, *x, Term::ZERO));
            }
            for i in 1..sz - 1 {
                for l in &by_size[i] {
                    for r in &by_size[sz - 1 - i] {
                        for o in [0usize, 1, 2, 3, 4] {
                            level.push(Term::op(o, *l, *r));
                        }
                    }
                }
            }
            by_size[sz] = level;
        }
        // the pool's terms and the patterns looked up in it use at most two variables (`abstractions(sub, 2)`), so signatures over
        // two give the same equalities as over `kv`, at 256 bytes instead of 4096 for the three-variable families
        let mut memo = ValueMemo::exhaustive(n, 2);
        let mut index: hashbrown::HashMap<Vec<u8>, Vec<Term>> = Default::default();
        for t in by_size.iter().flatten() {
            index.entry(memo.values(t).to_vec()).or_default().push(*t);
        }
        // `lt` terms (one-bit values) only as roots, indexed apart: their 0/1 values must not meet the n-bit constants
        let mut index_lt: hashbrown::HashMap<Vec<u8>, Vec<Term>> = Default::default();
        for a in by_size.iter().take(4).flatten() {
            for b in by_size.iter().take(4).flatten() {
                let t = Term::op(LT, *a, *b);
                index_lt.entry(memo.values(&t).to_vec()).or_default().push(t);
            }
        }
        println!("RULEMINER pool of {} terms, {} distinct functions", by_size.iter().map(|v| v.len()).sum::<usize>(), index.len());
        /// The patterns obtained from `t` by cutting subterms into variables: (pattern, cut subterms in variable order).
        fn abstractions(t: &Term, cap: usize) -> Vec<(Term, Vec<Term>)> {
            let mut out = vec![];
            if !matches!(*t.node(), Node::Zero | Node::Ones) {
                out.push((Term::v(0), vec![*t]));
            } else {
                out.push((*t, vec![]));
            }
            if let Node::Op(o, a, b) = *t.node() {
                for (pa, ca) in abstractions(&a, cap) {
                    for (pb, cb) in abstractions(&b, cap) {
                        // renumber the right pattern's variables after the left's, merging equal cut subterms
                        let mut cuts = ca.clone();
                        let mut map = vec![];
                        for c in &cb {
                            let at = cuts.iter().position(|x| x == c).unwrap_or_else(|| {
                                cuts.push(*c);
                                cuts.len() - 1
                            });
                            map.push(at);
                        }
                        if cuts.len() > cap {
                            continue;
                        }
                        fn renum(p: &Term, map: &[usize]) -> Term {
                            match *p.node() {
                                Node::V(i) => Term::v(map[i]),
                                Node::Op(o, a, b) => Term::op(o, renum(&a, map), renum(&b, map)),
                                _ => *p,
                            }
                        }
                        out.push((Term::op(o, pa, renum(&pb, &map)), cuts));
                    }
                }
            }
            out.retain(|(_, c)| c.len() <= cap);
            out
        }
        // RULEMINER_ANY=1: also abstract subterms without add/sub (constant folding inside shifts and bitwise nodes)
        let any_op = cfg.any_op;
        // patterns seen (`None`), and cross-side rules seen (`Some(rhs)`)
        let mut seen_pat: hashbrown::HashSet<(Term, Option<Term>)> = Default::default();
        let mut cands: Vec<(Term, Term)> = vec![];
        for st in &stragglers {
            let mut subs = vec![];
            st.3[0].subterms(&mut subs);
            st.3[1].subterms(&mut subs);
            for sub in subs.iter().filter(|t| matches!(*t.node(), Node::Op(LT, ..)) || (any_op || t.uses_add()) && t.size() >= if any_op { 2 } else { 3 }) {
                for (pat, _) in abstractions(sub, 2) {
                    let Node::Op(..) = *pat.node() else { continue };
                    if !seen_pat.insert((pat, None)) || pat.size() > 9 {
                        continue;
                    }
                    let is_lt = matches!(*pat.node(), Node::Op(LT, ..));
                    let Some(group) = (if is_lt { &index_lt } else { &index }).get(memo.values(&pat)) else { continue };
                    let uses = |t: &Term, v: usize| t.has_var(v);
                    let _ = is_lt;
                    for r in group.iter().filter(|r| ok_order(&pat, r) && (0..2).all(|v| !uses(r, v) || uses(&pat, v))) {
                        cands.push((pat, *r));
                    }
                }
            }
        }
        // cross-side candidates: a subterm of one normalized side and a subterm of the other with the same value, both
        // abstracted by the same cuts (up to four variables): the rule `abstract(s) -> abstract(s')`
        let cross_cap = cfg.vars;
        for st in &stragglers {
            let (mut sl, mut sr) = (vec![], vec![]);
            st.3[0].subterms(&mut sl);
            st.3[1].subterms(&mut sr);
            for (xs, ys) in [(&sl, &sr), (&sr, &sl)] {
                for x in xs.iter().filter(|t| t.uses_add() && t.size() >= 3 && t.size() <= 13) {
                    for y in ys.iter().filter(|t| t.size() <= 13 && *t != x) {
                        if !(1..=4).all(|w| x.plausibly_equals(y, w, kv)) {
                            continue;
                        }
                        for (pat, cuts) in abstractions(x, cross_cap) {
                            let Node::Op(..) = *pat.node() else { continue };
                            if cuts.len() <= 2 || pat.size() > 13 {
                                continue; // up to two variables is the pool route's job
                            }
                            // express y with the same cuts, through placeholders V(4+j)
                            let mut yy = *y;
                            for (j, c) in cuts.iter().enumerate() {
                                yy = replace_term(&yy, c, &Term::v(4 + j));
                            }
                            fn bare(t: &Term) -> bool {
                                match *t.node() {
                                    Node::V(i) => i >= 4,
                                    Node::Op(_, a, b) => bare(&a) && bare(&b),
                                    _ => true,
                                }
                            }
                            fn renum(t: &Term) -> Term {
                                match *t.node() {
                                    Node::V(i) => Term::v(i - 4),
                                    Node::Op(o, a, b) => Term::op(o, renum(&a), renum(&b)),
                                    _ => *t,
                                }
                            }
                            // renumbered only when bare: a cut-free variable below 4 has no index to take
                            if !bare(&yy) {
                                continue;
                            }
                            let rhs = renum(&yy);
                            // `x = y` holds for the straggler's variables, but the cuts become free variables, so the rule itself is checked:
                            // one that only held through a relation between the cuts would be scored every round and then fail its proof
                            if yy.size() < pat.size() + 4 && seen_pat.insert((pat, Some(rhs))) && (1..=4).all(|w| pat.plausibly_equals(&rhs, w, cuts.len())) {
                                // not ordered: orienting cross-side rules by the rule order raised M in every family (docs/tier-cycle.md,
                                // "A rewrite cycle"); a growing one can cycle with the built-in rules until the step budget runs out
                                cands.push((pat, rhs));
                            }
                        }
                    }
                }
            }
        }
        // extra candidates join the miner's own before the one-per-left-side pass
        if let Some(path) = &cfg.extra {
            let extra = read_rule_file(path);
            println!("RULEMINER {} extra candidates from {path}", extra.len());
            cands.extend(extra);
        }
        // `RULEMINER_NODUPLHS` (default on, 0 = off): drop candidates whose left side already has a rule in force (`RULEMINER_BASE`); the one-per-left-side pass
        // below only sees this mine's candidates, so a later mine could otherwise add a second, competing rewrite for the same pattern
        if cfg.no_dup_lhs {
            let before = cands.len();
            let in_force: hashbrown::HashSet<&Term> = base.iter().map(|(l, _)| l).collect();
            cands.retain(|(l, _)| !in_force.contains(l));
            println!("RULEMINER dropped {} candidates whose left side is already in force", before - cands.len());
        }
        // per left side, the smallest right side only, ties by `show()`. Scoring every right side instead (each left side's rival
        // orientations) fixed add3's `sub` chains but raised M on cmp3d and sbo3 and made cmp3d's mine 4.5x slower (docs/tier-cycle.md)
        // an identity (a pattern's pool group holds the pattern itself) never gains, and as the smallest right side it would displace
        // its left side's real candidates
        cands.retain(|(l, r)| l != r);
        cands.sort_by_cached_key(|(l, r)| (l.size(), l.show(), r.size(), r.show()));
        cands.dedup();
        // rivals: the other right sides of each left side; a round's winner gives way to a rival that gains more on the same laws,
        // unless the mine finished with the winner is worth more (the lookahead after the rounds' `pick`)
        // (docs/tier-cycle.md, "Preferences and rival orientations in the miner")
        let mut rivals: hashbrown::HashMap<Term, Vec<(Term, Term)>> = Default::default();
        for (l, r) in &cands {
            rivals.entry(*l).or_default().push((*l, *r));
        }
        rivals.values_mut().for_each(|v| {
            v.remove(0);
        });
        cands.dedup_by(|a, b| a.0 == b.0);
        println!("RULEMINER {} oriented candidates (one per left side)", cands.len());
        phase("candidate generation");
        // keep candidates whose left side matches a subterm of some straggler's normalized terms
        let applicable = |l: &Term| {
            stragglers.iter().any(|s| {
                let mut subs = vec![];
                s.3[0].subterms(&mut subs);
                s.3[1].subterms(&mut subs);
                subs.iter().any(|t| matches(l, t))
            })
        };
        let cands: Vec<(Term, Term)> = cands.into_iter().filter(|(l, _)| applicable(l)).take(trials).collect();
        println!("RULEMINER {} applicable candidates (cap {trials})", cands.len());
        if cfg.show {
            for (l, r) in &cands {
                println!("RULEMINER candidate: {} -> {}", l.show(), r.show());
            }
        }
        // each candidate is proved independently, on `RULEMINER_THREADS` workers; the proving reads the base rules and the step
        // budget of this thread, so the workers copy them. `RULEMINER_FAST` scores without rule proofs (`shared_lemma`), so there only a
        // round's winner is proved (`proved_lazily`), and an unprovable one gives way to the next best
        let (rules, budget) = (RULE_TABLE.with(|e| e.borrow().mined.clone()), RULE_BUDGET.with(|b| b.get()));
        let provable: Vec<&(Term, Term)> = if cfg.fast {
            cands.iter().collect()
        } else {
            let prove = |idx: &[usize]| -> Vec<usize> {
                tatic::kernel::scoped(|| {
                    set_extra_rules(rules.clone());
                    RULE_BUDGET.with(|b| b.set(budget));
                    idx.iter().copied().filter(|&i| prove_rule(n, cands[i].0.max_var().max(cands[i].1.max_var()) + 1, &cands[i].0, &cands[i].1).is_some()).collect()
                })
            };
            let threads = cfg.threads.clamp(1, 12);
            let mut ok: Vec<usize> = if threads == 1 {
                prove(&(0..cands.len()).collect::<Vec<_>>())
            } else {
                std::thread::scope(|sc| {
                    let handles: Vec<_> = (0..threads)
                        .map(|t| {
                            let idx: Vec<usize> = (t..cands.len()).step_by(threads).collect();
                            let prove = &prove;
                            std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, move || prove(&idx)).unwrap()
                        })
                        .collect();
                    handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
                })
            };
            ok.sort_unstable();
            ok.into_iter().map(|i| &cands[i]).collect()
        };
        println!("RULEMINER {} provable candidates of {} proposed", provable.len(), cands.len());
        phase("provable filter");
        // cumulative greedy: each round adds the candidate that, on top of the rules chosen so far, fixes the most
        // stragglers (no whole-term machine proof) and then shrinks the normalized terms most; a straggler often needs two
        // rules together, which a one-rule-at-a-time score cannot see
        // `score_laws` rewrites the scored laws `which` under the base rules plus `extra`: per law, whether it needs fewer machine proofs
        // than under the built-in rules alone, the size of its normalized terms (stragglers only) and, with `record`, every term
        // `rule_step` was asked about with the rule that fired on it, and every term the join examined. A candidate whose left side
        // matches none of the terms where it would come first (`Fired::preempted_by`: the run-time rules are tried most specific first,
        // not in the order added), and that is a join step at none of the join's terms (`Trace::touched_by`), cannot change a law's
        // rewriting or join, so its laws keep the result under the rules chosen so far.
        // `prefs`: the rule preferences in force (`set_rule_prefs`). `base_now`: the base rules in force, all of them until the
        // preference phase drops some
        let base_now = std::sync::Mutex::new(base.clone());
        let score_laws = |extra: &[(Term, Term)], prefs: &[Pref], which: &[usize], record: bool, seed: Option<RewriteMemo>| -> (Vec<(bool, i64, Trace)>, RewriteMemo) {
            let fallbacks = || MACHINE_FALLBACKS.with(|c| c.get());
            set_extra_rules(base_now.lock().unwrap().iter().chain(extra).cloned().collect());
            set_rule_prefs(prefs.to_vec());
            REWRITE_MEMO.with(|m| *m.borrow_mut() = Some(seed.unwrap_or_else(|| RewriteMemo::new(kv))));
            let steps = cfg.steps as i64;
            let budget = || RULE_BUDGET.with(|b| b.set(steps));
            // counting only under `RULEMINER_FAST`, or when the caller asked for it (rivals, below)
            let caller = SCORE_ONLY.with(|s| s.replace(cfg.fast || s.get()));
            let out = which
                .iter()
                .map(|&si| {
                    let s = &scored[si];
                    budget();
                    if record {
                        RULE_TRACE.with(|t| *t.borrow_mut() = Some(vec![]));
                    }
                    let before = fallbacks();
                    let ok = rewrite_plan(n, kv, &s.1, &s.2).is_some();
                    let fixed = ok && fallbacks() - before < s.4;
                    budget();
                    // the rule order's own measure: operator nodes first, then variable occurrences
                    let measure = |t: &Term| {
                        let mut occ = [0usize; 8];
                        t.occurrences(&mut occ);
                        let (c, a) = rule_weight(t);
                        (c + a.iter().sum::<i64>()) * 16 + occ.iter().sum::<usize>() as i64
                    };
                    let size = if si < stragglers.len() { measure(&rewrite(&s.1, n, kv).0) + measure(&rewrite(&s.2, n, kv).0) } else { 0 };
                    let mut seen: hashbrown::HashSet<(Term, Fired)> = Default::default();
                    let trace = Trace::new(RULE_TRACE.with(|t| t.borrow_mut().take()).unwrap_or_default().into_iter().filter(|t| seen.insert(*t)).collect());
                    (fixed, size, trace)
                })
                .collect();
            SCORE_ONLY.with(|s| s.set(caller));
            let memo = REWRITE_MEMO.with(|m| m.borrow_mut().take()).unwrap();
            set_extra_rules(vec![]);
            RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
            (out, memo)
        };
        let all_laws: Vec<usize> = (0..scored.len()).collect();
        let summarize = |ev: &[(bool, i64, Trace)]| (ev.iter().map(|e| e.0).collect::<Vec<bool>>(), ev.iter().map(|e| e.1).sum::<i64>());
        // under `RULEMINER_FAST` the candidates are proved here, once each, against the base rules as the eager filter would
        let proofs = std::cell::RefCell::new(vec![if cfg.fast { None } else { Some(true) }; provable.len()]);
        // also on a thread of its own (below): the base preferences, which every evaluation on this thread leaves installed
        let prove_any = |(l, r): &(Term, Term)| -> bool {
            tatic::kernel::scoped(|| {
                set_extra_rules(rules.clone());
                set_rule_prefs(base_prefs.clone());
                RULE_BUDGET.with(|b| b.set(budget));
                let ok = prove_rule(n, l.max_var().max(r.max_var()) + 1, l, r).is_some();
                set_extra_rules(vec![]);
                RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
                ok
            })
        };
        // a round's winner is proved on a thread of its own while the next round is scored (`speculate`, set for the main path's
        // rounds and lookahead's greedy paths): the round takes it as provable (`assumed`) and is committed when its proof is in,
        // and a failed proof rolls the rounds back to it (below). Any other proof of a pending candidate waits for its result
        let (proof_tx, proof_rx) = std::sync::mpsc::channel::<(usize, bool)>();
        let pending: std::cell::RefCell<hashbrown::HashSet<usize>> = Default::default();
        let (speculate, spawn_req) = (std::cell::Cell::new(false), std::cell::Cell::new(None::<usize>));
        let assumed: std::cell::RefCell<Vec<usize>> = Default::default();
        let resolve = |i: usize| -> bool {
            loop {
                if let Some(b) = proofs.borrow()[i] {
                    return b;
                }
                let (j, b) = proof_rx.recv().unwrap();
                pending.borrow_mut().remove(&j);
                proofs.borrow_mut()[j] = Some(b);
            }
        };
        let prove_one = |i: usize| if pending.borrow().contains(&i) { resolve(i) } else { prove_any(provable[i]) };
        // the rules chosen so far and, under them, each law's evaluation, the stragglers and guard laws they cover and the total size
        struct Chosen {
            chosen: Vec<(Term, Term)>,
            eval: Vec<(bool, i64, Trace)>,
            covered: Vec<bool>,
            size: i64,
        }
        // the last evaluation's memo, under its rules: an entry holds under other rules when no rule in or out touches a term of its
        // trace (`RewriteMemo::filtered`), so each evaluation is seeded with what the rules that changed cannot touch
        let key = |c: &[(Term, Term)]| {
            let mut v = c.to_vec();
            v.sort();
            v
        };
        let state_memo: std::cell::RefCell<Option<(Vec<(Term, Term)>, RewriteMemo)>> = Default::default();
        let state_time = std::cell::Cell::new(std::time::Duration::ZERO);
        // the join's work on this thread and the scoring workers (`JoinCost`), and the time spent bounding the candidates' gains
        let (join_main, join_workers) = (JoinCost::now(), std::sync::Mutex::new(JoinCost::default()));
        let bound_time = std::cell::Cell::new(std::time::Duration::ZERO);
        let state = |chosen: Vec<(Term, Term)>| {
            let t0 = Instant::now();
            let seed = state_memo.borrow_mut().take().map(|(was, memo)| {
                let changed: Vec<&(Term, Term)> = was.iter().chain(&chosen).filter(|r| was.contains(*r) != chosen.contains(*r)).collect();
                memo.filtered(|tr| !changed.iter().any(|r| tr.touched_by(r, |_| true)))
            });
            let (eval, grown) = score_laws(&chosen, &base_prefs, &all_laws, true, seed);
            *state_memo.borrow_mut() = Some((chosen.clone(), grown));
            let (covered, size) = summarize(&eval);
            state_time.set(state_time.get() + t0.elapsed());
            Chosen { chosen, eval, covered, size }
        };
        let count = |f: &Vec<bool>| f.iter().take(stragglers.len()).filter(|c| **c).count() as i64;
        let guarded = |f: &Vec<bool>| f.iter().skip(stragglers.len()).filter(|c| **c).count() as i64;
        // what a round's gain measures, as a total: a rule's gain is the value it adds
        let value = |s: &Chosen| count(&s.covered) * 1000 + guarded(&s.covered) * guard_w - s.size;
        let (law_evals, law_reuses) = (std::sync::atomic::AtomicUsize::new(0), std::sync::atomic::AtomicUsize::new(0));
        let (scorings, skipped) = (std::cell::Cell::new(0usize), std::cell::Cell::new(0usize));
        // one round on top of `s`: its alternatives with their gains, largest first: a rival orientation of the winner that gains
        // more, if one is proved, then the winner
        let pick = |s: &Chosen| -> Vec<((Term, Term), i64)> {
            let (chosen, base_eval, covered, size) = (&s.chosen, &s.eval, &s.covered, s.size);
            // a candidate changes only the laws whose rewriting asked about a term its left side matches, or whose join examined a
            // term it is a step at (`affected`, `Trace::touched_by`), so its gain is at most
            // 1000 per affected uncovered straggler, `guard_w` per affected uncovered guard law and the affected stragglers' whole size
            // a candidate can only rewrite a term where it comes before the rule that fired (`Fired::preempted_by`), unless a
            // preference makes it a winner (the trace was made without the candidate)
            // the run-time order of every rule in play, ranked once (`run_order` builds strings)
            let t0 = Instant::now();
            let mut ranked: Vec<(Term, Term)> = base_now.lock().unwrap().iter().chain(chosen).chain(provable.iter().copied()).cloned().collect();
            ranked.sort_by_cached_key(|(l, r)| run_order(l, r));
            let rank: hashbrown::HashMap<(Term, Term), usize> = ranked.into_iter().enumerate().map(|(i, r)| (r, i)).collect();
            // every law's trace at once (`TraceIndex`: a term shared by many laws' traces is matched once), the candidates split
            // over the scoring threads; each candidate's laws are the same whichever thread finds them
            let index = TraceIndex::new(base_eval.iter().map(|e| &e.2));
            let touched = |rule: &(Term, Term)| {
                let anywhere = base_prefs.iter().any(|(w, _)| w == rule);
                let before = |fired: &(Term, Term)| rank.get(fired).is_none_or(|&f| rank[rule] < f);
                index.touched(rule, |fired| anywhere || fired.preempted_by(before))
            };
            let threads = cfg.threads.clamp(1, 12);
            let affected: Vec<Vec<usize>> = std::thread::scope(|sc| {
                let handles: Vec<_> = (0..threads)
                    .map(|t| {
                        let (touched, provable) = (&touched, &provable);
                        sc.spawn(move || (t..provable.len()).step_by(threads).map(|i| touched(provable[i])).collect::<Vec<_>>())
                    })
                    .collect();
                let mut parts: Vec<_> = handles.into_iter().map(|h| h.join().unwrap().into_iter()).collect();
                (0..provable.len()).map(|i| parts[i % threads].next().unwrap()).collect()
            });
            let bound = |i: usize| -> i64 {
                let gain = |si: usize, w: i64| if covered[si] { 0 } else { w };
                affected[i].iter().map(|&si| if si < stragglers.len() { gain(si, 1000) + base_eval[si].1 } else { gain(si, guard_w) }).sum()
            };
            let mut order: Vec<(i64, usize)> = (0..provable.len()).map(|i| (bound(i), i)).collect();
            order.sort_by_key(|&(b, i)| (std::cmp::Reverse(b), i));
            bound_time.set(bound_time.get() + t0.elapsed());
            // the candidates are scored on `RULEMINER_THREADS` workers (default 1; keep at most 12), each with its own intern
            // scope, a chunk at a time in order of their bound; scoring stops at a bound below the best gain so far, since those
            // candidates cannot win, so the choice does not depend on the thread count or the chunking. Each candidate is scored from
            // an empty memo: a memo kept across a worker's candidates made a gain depend on which candidates that worker scored before
            // (its join entries are inexact by design), so the choice depended on scheduling, and it saved no time (docs/decisions/
            // 2026-10-17-monotone-join.md, "Spike of the snapshot"). The join store is shared instead, read-only: the workers read
            // the copy frozen as the round starts, which only this thread's searches fed (docs/tier-cycle.md, "Spike of the join
            // store"). Expressions are per thread, so each worker grows its own (1.5x
            // faster scoring on cmp3d, docs/tier-cycle.md, "Miner speedups")
            // a rule's gain on top of the rules chosen so far; it changes only the laws `aff` it can touch
            let score_rule = |rule: &(Term, Term), aff: &[usize]| -> (i64, Vec<bool>, i64) {
                let mut with = chosen.clone();
                with.push(*rule);
                let (fresh, _) = score_laws(&with, &base_prefs, aff, true, None);
                law_evals.fetch_add(all_laws.len(), std::sync::atomic::Ordering::Relaxed);
                law_reuses.fetch_add(all_laws.len() - aff.len(), std::sync::atomic::Ordering::Relaxed);
                let mut ev: Vec<(bool, i64)> = base_eval.iter().map(|e| (e.0, e.1)).collect();
                for (&si, f) in aff.iter().zip(&fresh) {
                    ev[si] = (f.0, f.1);
                }
                let (f, sz) = (ev.iter().map(|e| e.0).collect::<Vec<bool>>(), ev.iter().map(|e| e.1).sum::<i64>());
                ((count(&f) - count(covered)) * 1000 + (guarded(&f) - guarded(covered)) * guard_w + (size - sz), f, sz)
            };
            // the winner's left side with another right side: same affected laws, proved only if it would win
            // rivals are not proved before scoring, so they are scored by counting only (`SCORE_ONLY`); scoring compiles no plans, so an
            // unprovable rival (`sub(x, shl1(x, 0)) -> sub(shr1(0, 0), x)` once the promoted rules are out) is never proved
            let rivals_of = |i: usize| rivals.get(&provable[i].0).map_or(&[][..], |v| &v[..]);
            // a job: candidate `i`, or with `Some(k)` the `k`th rival of the winner `i`
            let score_job = |(i, k): (usize, Option<usize>)| match k {
                None => score_rule(provable[i], &affected[i]),
                Some(k) => {
                    let fast = SCORE_ONLY.with(|s| s.replace(true));
                    let r = score_rule(&rivals_of(i)[k], &affected[i]);
                    SCORE_ONLY.with(|s| s.set(fast));
                    r
                }
            };
            // best gain first, ties to the earlier candidate; the first one that is proved wins, and an unprovable one reopens the
            // candidates whose bound reaches the next best
            let mut results: Vec<Option<(i64, Vec<bool>, i64)>> = vec![None; provable.len()];
            let mut next = 0;
            let (winner, rival_gains) = std::thread::scope(|sc| {
                // one queue for all workers: each takes the next candidate when it is free, so a chunk ends when its last
                // candidate is scored rather than when the slowest worker's fixed share is; the winner's rivals go through it too,
                // each scored on its own, so their gains do not depend on which worker scored them
                let (done_tx, done_rx) = std::sync::mpsc::channel();
                let (work, queue) = std::sync::mpsc::channel::<(usize, Option<usize>)>();
                let queue = std::sync::Arc::new(std::sync::Mutex::new(queue));
                // the join store as this round starts, for the workers
                let frozen = frozen_join_store();
                for _ in 0..threads {
                    let (done_tx, score_job, queue, join_workers, frozen) = (done_tx.clone(), &score_job, queue.clone(), &join_workers, frozen.clone());
                    let worker = move || {
                        set_join_store(frozen.map(JoinStoreUse::Read));
                        let before = JoinCost::now();
                        tatic::kernel::scoped(|| {
                            loop {
                                let Ok(job) = queue.lock().unwrap().recv() else { break };
                                done_tx.send((job, score_job(job))).unwrap();
                            }
                        });
                        join_workers.lock().unwrap().add_since(before);
                    };
                    std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, worker).unwrap();
                }
                let winner = loop {
                    let best = (0..provable.len()).filter(|&i| proofs.borrow()[i] != Some(false)).filter_map(|i| results[i].as_ref().map(|r| (r.0, i))).filter(|r| r.0 > 0).max_by_key(|&(g, i)| (g, std::cmp::Reverse(i)));
                    let floor = best.map_or(1, |b| b.0);
                    let chunk: Vec<usize> = order[next..].iter().take_while(|&&(b, _)| b >= floor).take(threads * 4).map(|&(_, i)| i).collect();
                    if chunk.is_empty() {
                        let Some((_, i)) = best else { break None };
                        let known = proofs.borrow()[i];
                        let ok = match known {
                            Some(ok) => ok,
                            None if speculate.get() => {
                                assumed.borrow_mut().push(i);
                                if pending.borrow_mut().insert(i) {
                                    spawn_req.set(Some(i));
                                }
                                true
                            }
                            None => {
                                let ok = prove_one(i);
                                proofs.borrow_mut()[i] = Some(ok);
                                ok
                            }
                        };
                        if ok {
                            break Some(i);
                        }
                        continue;
                    }
                    next += chunk.len();
                    for &i in &chunk {
                        work.send((i, None)).unwrap();
                    }
                    for ((i, _), r) in done_rx.iter().take(chunk.len()) {
                        results[i] = Some(r);
                    }
                };
                let mut gains = vec![0; winner.map_or(0, |i| rivals_of(i).len())];
                for k in 0..gains.len() {
                    work.send((winner.unwrap(), Some(k))).unwrap();
                }
                for ((_, k), r) in done_rx.iter().take(gains.len()) {
                    gains[k.unwrap()] = r.0;
                }
                (winner, gains)
            });
            scorings.set(scorings.get() + next);
            skipped.set(skipped.get() + provable.len() - next);
            phase(&format!("round over {} of {} candidates", next, provable.len()));
            let Some(i) = winner else { return vec![] };
            let g = results[i].as_ref().unwrap().0;
            // in the rivals' order, as when they were scored one after another here
            let mut rival: Option<((Term, Term), i64)> = None;
            for (rv, &rg) in rivals_of(i).iter().zip(&rival_gains) {
                if rg > rival.as_ref().map_or(g, |r| r.1) && prove_any(rv) {
                    rival = Some((*rv, rg));
                }
            }
            rival.into_iter().chain([(*provable[i], g)]).collect()
        };
        // a rival's larger round gain can lead to a worse finished set (docs/tier-cycle.md, "The cold loss is a greedy path loss"), so
        // both are finished greedily (rivals taken, no lookahead) and the better finished set's choice is kept, ties to the rival.
        // Looking ahead over runners-up too lost ("Lookahead on rival swaps")
        let then = |s: &Chosen, rule: &(Term, Term)| state(s.chosen.iter().chain([rule]).cloned().collect());
        // a round depends only on the set of rules chosen so far (`set_extra_rules` sorts them), and alternatives' greedy paths often
        // reach the same set in another order, so picks and finished values are kept by set; the kept alternative's path is also the
        // next rounds' own (`key`, above)
        #[allow(clippy::type_complexity)]
        let picks: std::cell::RefCell<hashbrown::HashMap<Vec<(Term, Term)>, Vec<((Term, Term), i64)>>> = Default::default();
        let pick_kept = |s: &Chosen| {
            let kk = key(&s.chosen);
            if let Some(v) = picks.borrow().get(&kk) {
                return v.clone();
            }
            let v = pick(s);
            picks.borrow_mut().insert(kk, v.clone());
            v
        };
        // a set's finished value and the rounds finishing took, valid under any cap of at least that many rounds
        let finished: std::cell::RefCell<hashbrown::HashMap<Vec<(Term, Term)>, (i64, usize)>> = Default::default();
        // the value of `chosen` finished greedily (each round's first alternative) in at most `rounds` more rounds; while
        // speculating, each pick's assumed winner is proved on a thread of its own (`spawn`)
        let finish = |mut chosen: Vec<(Term, Term)>, rounds: usize, spawn: &dyn Fn(usize)| -> i64 {
            let (mut path, mut left) = (vec![], rounds);
            let (v, mut d) = loop {
                let kk = key(&chosen);
                if let Some(&(v, d)) = finished.borrow().get(&kk).filter(|e| e.1 <= left) {
                    break (v, d);
                }
                let s = state(chosen);
                if left == 0 {
                    return value(&s); // cut by the round cap: not kept
                }
                let alts = pick_kept(&s);
                if let Some(j) = spawn_req.take() {
                    spawn(j);
                }
                let Some((rule, _)) = alts.into_iter().next() else {
                    let v = value(&s);
                    finished.borrow_mut().insert(kk, (v, 0));
                    break (v, 0);
                };
                path.push(kk);
                chosen = s.chosen;
                chosen.push(rule);
                left -= 1;
            };
            for kk in path.into_iter().rev() {
                d += 1;
                finished.borrow_mut().insert(kk, (v, d));
            }
            v
        };
        // rounds not yet committed, oldest first: the state before each, its round, its winner's pending proof and its `chosen` line
        struct Open {
            before: Chosen,
            round: usize,
            proof: Option<usize>,
            line: String,
            rule: String,
        }
        // commits the open rounds whose proofs hold, oldest first, until `keep` are left; at a failed proof, voids the rounds built
        // on it (their picks too, as the failed winner is never picked again) and returns it, to be played again
        let settle = |open: &mut Vec<Open>, keep: usize| -> Option<Open> {
            while open.len() > keep {
                let o = open.remove(0);
                if o.proof.is_none_or(&resolve) {
                    println!("{}", o.line);
                    crate::task::result("chosen", &o.rule);
                    continue;
                }
                println!("RULEMINER rolled back to round {}: its winner {} is not provable", o.round, o.proof.map_or(String::new(), |i| rule_show(provable[i])));
                for v in std::iter::once(&o).chain(open.iter()) {
                    picks.borrow_mut().remove(&key(&v.before.chosen));
                }
                for v in open.drain(..) {
                    v.proof.map(resolve);
                }
                return Some(o);
            }
            None
        };
        let s = std::thread::scope(|sc| {
            let spawn = |i: usize| {
                let (tx, rule, prove_any) = (proof_tx.clone(), provable[i], &prove_any);
                std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, move || tx.send((i, prove_any(rule))).unwrap()).unwrap();
            };
            let (mut s, mut round, mut open) = (state(vec![]), 0, Vec::<Open>::new());
            loop {
                speculate.set(true);
                let alts = if round < cfg.rounds { pick_kept(&s) } else { vec![] };
                speculate.set(false);
                // the main path's assumption is the round's own pending proof (`proof`)
                assumed.borrow_mut().clear();
                let proof = spawn_req.take();
                proof.map(spawn);
                let Some(mut rule) = alts.first().map(|a| a.0) else {
                    match settle(&mut open, 0) {
                        Some(o) => (s, round) = (o.before, o.round),
                        None => break s,
                    }
                    continue;
                };
                if alts.len() > 1 {
                    // lookahead plays whole greedy paths from settled rounds, taking each pick's winner as provable while it is proved
                    // in the background; a path that took an unprovable winner voids the picks that offered it and the finished values
                    // (any may rest on it), and the paths are played again
                    if let Some(o) = settle(&mut open, 0) {
                        (s, round) = (o.before, o.round);
                        continue;
                    }
                    if !proof.is_none_or(resolve) {
                        println!("RULEMINER rolled back to round {round}: its winner {} is not provable", proof.map_or(String::new(), |i| rule_show(provable[i])));
                        picks.borrow_mut().remove(&key(&s.chosen));
                        continue;
                    }
                    let rest = cfg.rounds - round - 1;
                    let values = loop {
                        speculate.set(true);
                        let values: Vec<i64> = alts.iter().map(|(r, _)| finish(s.chosen.iter().chain([r]).cloned().collect(), rest, &spawn)).collect();
                        speculate.set(false);
                        let failed: Vec<usize> = assumed.take().into_iter().filter(|&i| !resolve(i)).collect();
                        if failed.is_empty() {
                            break values;
                        }
                        println!("RULEMINER lookahead played again: {} is not provable", failed.iter().map(|&i| rule_show(provable[i])).collect::<Vec<_>>().join(", "));
                        picks.borrow_mut().retain(|_, v| !v.iter().any(|(r, _)| failed.iter().any(|&i| provable[i] == r)));
                        finished.borrow_mut().clear();
                    };
                    let best = (0..alts.len()).max_by_key(|&a| (values[a], std::cmp::Reverse(a))).unwrap();
                    for (a, ((l, r), g)) in alts.iter().enumerate() {
                        println!("RULEMINER lookahead: {} {} -> {} (+{g}) finishes at {}", if a == best { "keep" } else { "    " }, l.show(), r.show(), values[a]);
                    }
                    rule = alts[best].0;
                }
                let next = then(&s, &rule);
                let line = format!("RULEMINER chosen (+{} fixed, -{} size): {} -> {}", count(&next.covered) - count(&s.covered), s.size - next.size, rule.0.show(), rule.1.show());
                phase("rule-set evaluation");
                open.push(Open { before: s, round, proof, line, rule: rule_show(&rule) });
                (s, round) = (next, round + 1);
                // the newest three rounds stay open: a winner's proof (about 87 ms on cmp3d) runs while the next three rounds are
                // scored (about 60 ms each at 6 threads); docs/tier-cycle.md, "Why six threads gave little"
                if let Some(o) = settle(&mut open, 3) {
                    (s, round) = (o.before, o.round);
                }
            }
        });
        let Chosen { chosen, covered, .. } = s;
        let (scorings, skipped) = (scorings.get(), skipped.get());
        // learned preferences (docs/tier-cycle.md, "Rule order"): where two rules in force both rewrite a term of the scored laws, the
        // first one in order does; each round tries letting the other win, one pair at a time, and dropping each unit of a pooled base
        // (`drop_units`: the rules where one library's normal forms meet another's), and keeps the move with the largest gain (the
        // rule rounds' gain), until none gains. Only with `RULEMINER_PREFS=1`: a family's own rules rarely conflict, so the phase pays
        // off on a pooled library (`driver::sweep`) and barely in a loop's mines, where it doubled the mine time ("Preferences and
        // rival orientations in the miner")
        // `RULEMINER_UNITS=<file>`: the base's drop units (`joinability_units`, built once per pooled library by `driver::sweep`)
        let units = cfg.units.as_ref().filter(|_| cfg.prefs).map_or(vec![], |f| parse_units(&std::fs::read_to_string(f).unwrap()));
        for (u, rules) in units.iter().enumerate() {
            println!("RULEMINER drop unit {u}: {}", rules.iter().map(|(l, r)| format!("{} -> {}", l.show(), r.show())).collect::<Vec<_>>().join("; "));
        }
        let mut dropped: Vec<usize> = vec![];
        let set_base = |dropped: &[usize]| {
            *base_now.lock().unwrap() = base.iter().filter(|r| !dropped.iter().any(|&u| units[u].contains(r))).cloned().collect();
        };
        let mut prefs = base_prefs.clone();
        while cfg.prefs {
            *RULE_CONFLICTS.get(Default::default).lock().unwrap() = Some(Default::default());
            let (now, _) = score_laws(&chosen, &prefs, &all_laws, false, None);
            let mut conflicts: Vec<Pref> = RULE_CONFLICTS.get(Default::default).lock().unwrap().take().unwrap().into_keys().collect();
            let shown = |(w, l): &Pref| (rule_show(w), rule_show(l));
            conflicts.sort_by_cached_key(shown);
            let (f0, size0) = summarize(&now);
            let gain = |prefs: &[Pref]| {
                let (f, sz) = summarize(&score_laws(&chosen, prefs, &all_laws, false, None).0);
                (count(&f) - count(&f0)) * 1000 + (guarded(&f) - guarded(&f0)) * guard_w + (size0 - sz)
            };
            // a flip's move key is the pair it makes (winner, loser); a drop's is its unit's index
            let flipped = |(w, l): &Pref| prefs.iter().filter(|p| (&p.0, &p.1) != (l, w)).cloned().chain([(*w, *l)]).collect::<Vec<_>>();
            let mut moves: Vec<(i64, Result<Pref, usize>)> = conflicts.iter().map(|(w, l)| (*l, *w)).map(|f| (gain(&flipped(&f)), Ok(f))).collect();
            for u in (0..units.len()).filter(|u| !dropped.contains(u)) {
                set_base(&[&dropped[..], &[u]].concat());
                moves.push((gain(&prefs), Err(u)));
            }
            set_base(&dropped);
            // a drop removes many rules at once, so it needs two laws' worth of gain: on one law it overfit (salt 1's sbo3)
            // ties to the first move in text order
            let text = |m: &Result<Pref, usize>| m.as_ref().map(shown).map_err(|u| *u);
            let best = moves.into_iter().filter(|(g, m)| *g > if m.is_err() { 1999 } else { 0 }).max_by(|a, b| a.0.cmp(&b.0).then_with(|| text(&b.1).cmp(&text(&a.1))));
            phase(&format!("preference round over {} conflicts and {} drop units", conflicts.len(), units.len() - dropped.len()));
            match best {
                None => break,
                Some((g, Ok((w, l)))) => {
                    println!("RULEMINER prefer (+{g} gain): {}  OVER  {}", rule_show(&w), rule_show(&l));
                    crate::task::result("prefer", format!("{}  OVER  {}", rule_show(&w), rule_show(&l)));
                    prefs = flipped(&(w, l));
                }
                Some((g, Err(u))) => {
                    for (l, r) in &units[u] {
                        println!("RULEMINER drop (+{g} gain): {} -> {}", l.show(), r.show());
                        crate::task::result("drop", format!("{} -> {}", l.show(), r.show()));
                    }
                    dropped.push(u);
                    set_base(&dropped);
                }
            }
        }
        println!("RULEMINER scoring reused {} of {} law evaluations", law_reuses.load(std::sync::atomic::Ordering::Relaxed), law_evals.load(std::sync::atomic::Ordering::Relaxed));
        println!("RULEMINER the gain bound skipped {skipped} of {} candidate scorings", scorings + skipped);
        if cfg.fast {
            let p = proofs.borrow();
            println!("RULEMINER lazy proofs: {} proved, {} failed", p.iter().filter(|x| **x == Some(true)).count(), p.iter().filter(|x| **x == Some(false)).count());
        }
        println!("RULEMINER time in rule-set evaluations: {:.1}s", state_time.get().as_secs_f64());
        println!("RULEMINER time bounding candidates' gains: {:.1}s", bound_time.get().as_secs_f64());
        let mut j = *join_workers.lock().unwrap();
        j.add_since(join_main);
        println!("RULEMINER join: {} searches reaching {} terms, {} met, {} memo hits, {:.1}s searching ({:.1}s in failed searches)", j.searches, j.reached, j.met, j.hits, j.nanos as f64 / 1e9, j.failed_nanos as f64 / 1e9);
        println!("RULEMINER join store: {} joins served, {:.1}s querying", j.stored, j.store_nanos as f64 / 1e9);
        println!("RULEMINER {} of {} stragglers covered by the chosen rules", covered.iter().take(stragglers.len()).filter(|c| **c).count(), stragglers.len());
        for (st, c) in stragglers.iter().zip(&covered) {
            if !c {
                println!("RULEMINER uncovered: {}", st.0);
            }
        }
        set_join_store(None);
    });
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

/// `read_rule_file` (behind `RULEMINER_EXTRA`) parses `lhs -> rhs` lines and skips comments and blanks.
#[test]
pub fn extra_candidates_are_merged() {
    let path = std::env::temp_dir().join(format!("extra_candidates_{}.txt", std::process::id()));
    std::fs::write(&path, "# comment\n\nadd(sub(x, y), z) -> add(sub(z, y), x)\nand(x, x) -> x\n").unwrap();
    let rules = read_rule_file(path.to_str().unwrap());
    std::fs::remove_file(&path).ok();
    let shown: Vec<(String, String)> = rules.iter().map(|(l, r)| (l.show(), r.show())).collect();
    assert_eq!(shown.len(), 2, "{shown:?}");
    assert_eq!(shown[0], (parse_term("add(sub(x, y), z)").show(), parse_term("add(sub(z, y), x)").show()));
    assert_eq!(shown[1], (parse_term("and(x, x)").show(), parse_term("x").show()));
}

#[test]
pub fn notsub_rule_is_provable() {
    tatic::kernel::scoped(|| {
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        for n in [3, 4] {
            let r = prove_rule(n, 1, &op(3, Term::v(0), Term::ONES), &op(4, Term::ONES, Term::v(0)));
            let (p, s) = r.expect("xor(x, -1) = sub(-1, x)");
            ck("notsub", &p, &s);
        }
    })
}

/// `rewrite_law` closes `lt` laws: operands rewritten under the root, then congruence; a false law is refused.
#[test]
pub fn rewrite_law_proves_lt_laws() {
    tatic::kernel::scoped(|| {
        let (x, y) = (Term::v(0), Term::v(1));
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let n = 4;
        for (name, t1, t2) in [
            ("lt (x + 0) y = lt x y", op(5, op(0, x, Term::ZERO), y), op(5, x, y)),
            ("lt (x + y) y = lt (y + x) y", op(5, op(0, x, y), y), op(5, op(0, y, x), y)),
            ("lt (x + y) (x + x) = lt (y + x) (x + x)", op(5, op(0, x, y), op(0, x, x)), op(5, op(0, y, x), op(0, x, x))),
        ] {
            let (p, s) = rewrite_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no proof"));
            ck(name, &p, &s);
        }
        assert!(rewrite_law(n, 2, &op(5, x, y), &op(5, y, x)).is_none());
    })
}

#[test]
pub fn lt_rules_with_constant_right_sides_are_provable() {
    tatic::kernel::scoped(|| {
        let lt = |a: Term, b: Term| Term::op(LT, a, b);
        let n = 4;
        for k in [1usize, 2] {
            for (l, r) in [(lt(Term::ONES, Term::v(0)), lt(Term::ONES, Term::ONES)), (lt(Term::v(0), Term::v(0)), lt(Term::ONES, Term::ONES))] {
                let (p, s) = prove_rule(n, k, &l, &r).unwrap_or_else(|| panic!("k={k}: {} -> {}", l.show(), r.show()));
                ck("lt rule", &p, &s);
            }
        }
    })
}

/// Two root rules close `lt(x, x) = lt(-1, x + y)` without a machine proof of the whole law.
#[test]
pub fn lt_root_rules_close_constant_false_laws() {
    tatic::kernel::scoped(|| {
        let (x, y) = (Term::v(0), Term::v(1));
        let lt = |a: Term, b: Term| Term::op(LT, a, b);
        let add = |a: Term, b: Term| Term::op(ADD, a, b);
        let falsum = lt(Term::ONES, Term::ONES);
        set_extra_rules(vec![(lt(x, x), falsum), (lt(Term::ONES, x), falsum)]);
        let before = MACHINE_FALLBACKS.with(|c| c.get());
        let r = rewrite_law(4, 2, &lt(x, x), &lt(Term::ONES, add(x, y)));
        let fell = MACHINE_FALLBACKS.with(|c| c.get()) - before;
        set_extra_rules(vec![]);
        let (p, s) = r.expect("proved");
        ck("lt(x,x) = lt(-1, x+y)", &p, &s);
        assert_eq!(fell, 0, "no whole-term machine proof");
    })
}

#[test]
pub fn shr_mask_proves_root_shift_laws_over_arithmetic_and_rejects_false_ones() {
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
                let (p, s) = rewrite_law(n, 2, l, r).unwrap_or_else(|| panic!("no proof: {} = {} at n={n}", l.show(), r.show()));
                ck(&format!("{} = {} at n={n}", l.show(), r.show()), &p, &s);
            }
        }
        // not laws: the arguments differ above bit 0
        for (l, r) in [(shr(op(0, v(0), v(1))), shr(op(0, v(0), v(0)))), (Term::ZERO, shr(op(0, v(0), Term::ONES)))] {
            assert!(rewrite_law(4, 2, &l, &r).is_none(), "{} = {}", l.show(), r.show());
        }
    })
}

/// Lemma ablation, end to end (search note section 51): the library lemmas `add x 0 = x`, `add 0 x = x`, `add x y = add y x`,
/// `add x ~x = -1` and associativity are proved from the statement alone, by the Moore-refinement encoding search inside
/// `add_tree_law` (no rewrite rule, no hand-written invariant), and checked by the kernel at several widths.
#[test]
pub fn encoding_search_rediscovers_library_lemmas_from_statements() {
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
                let (p, s) = add_tree_law(n, *k, l, r).unwrap_or_else(|| panic!("no proof: {name} at n={n}"));
                ck(&format!("{name} at n={n}"), &p, &s);
            }
        }
        // a non-law is refused
        assert!(add_tree_law(4, 2, &op(0, v(0), v(1)), &op(0, v(0), v(0))).is_none());
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
pub fn rule_admissible(l: &Term, r: &Term) -> bool {
    rule_order_ok(l, r) && [3usize, 4].iter().all(|&n| prove_rule(n, l.max_var().max(r.max_var()) + 1, l, r).is_some())
}

#[test]
pub fn promoted_rules_are_ordered_and_provable() {
    tatic::kernel::scoped(|| {
        for (l, r) in promoted_rules() {
            assert_eq!(parse_term(&l.show()).show(), l.show());
            assert!(rule_admissible(l, r), "{} -> {} is not decreasing in the rule order or not provable at widths 3 and 4", l.show(), r.show());
        }
    })
}

/// The admission test refuses wrong rules: every promoted rule with its right side replaced by another promoted rule's
/// right side over the same variables (so it stays well-formed and, where the order allows, decreasing) is refused unless
/// it happens to be a true law.
#[test]
pub fn rule_admission_refuses_wrong_rules() {
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
                    assert!(!rule_admissible(l, r), "wrong rule admitted: {} -> {}", l.show(), r.show());
                    refused += 1;
                }
            }
        }
        println!("ADMISSION {refused} wrong rules refused of {tried} tried");
        assert!(refused > 50, "too few wrong rules exercised: {refused}");
    })
}

/// Probe (search note section 61): the 7 non-constant `lt` stragglers restated through the borrow bit, at width 4.
/// `lt(a, b)` is the top bit of `B(a, b) = (~a & b) | (~(a ^ b) & (a - b))`, so `lt(a, b) = lt(c, d)` becomes the
/// shift-free law `B(a, b) & TOP = B(c, d) & TOP` (`TOP` = 8). Prints, per law, whether the rewriter proves it and how many
/// whole-term machine proofs it still needed, next to the same count for the `lt` form.
#[test]
#[ignore]
pub fn lt_borrow_bit_probe() {
    tatic::kernel::scoped(|| {
        let b = |o: usize, a: Term, c: Term| Term::op(o, a, c);
        let not = |a: Term| b(3, a, Term::ONES);
        let one = b(4, Term::ZERO, Term::ONES);
        let top = b(6, b(6, b(6, one, Term::ZERO), Term::ZERO), Term::ZERO);
        let borrow = |t: &Term| -> Term {
            let Node::Op(LT, x, y) = *t.node() else { panic!("not an lt") };
            b(2, b(1, not(x), y), b(1, not(b(3, x, y)), b(4, x, y)))
        };
        let laws = [
            ("lt(0, xor(x, y))", "lt(and(0, y), sub(y, x))"),
            ("lt(add(x, x), x)", "lt(sub(-1, x), xor(x, 0))"),
            ("lt(add(x, y), -1)", "lt(xor(y, x), or(0, -1))"),
            ("lt(add(y, y), y)", "lt(sub(-1, y), and(y, y))"),
            ("lt(x, add(x, x))", "lt(or(0, x), sub(0, x))"),
            ("lt(x, xor(y, -1))", "lt(or(y, 0), xor(-1, x))"),
            ("lt(y, add(y, y))", "lt(xor(y, 0), sub(0, y))"),
        ];
        for (l, r) in laws {
            let (l, r) = (parse_term(l), parse_term(r));
            let fall = || MACHINE_FALLBACKS.with(|c| c.get());
            let before = fall();
            let direct = rewrite_plan(4, 2, &l, &r).is_some();
            let direct_fell = fall() - before;
            let (bl, br) = (b(1, borrow(&l), top), b(1, borrow(&r), top));
            let before = fall();
            let via = rewrite_plan(4, 2, &bl, &br).is_some();
            println!("BORROW {} = {}: lt form proved={direct} machine proofs {direct_fell}; borrow form proved={via} machine proofs {}", l.show(), r.show(), fall() - before);
        }
    })
}

/// Soundness sweep (search note section 64). `SWEEP_FAMILY` (mul, shl, lt, shr; sized by the `RULEMINER_*` vars),
/// `SWEEP_WIDTHS` (default `3,4`). (A) Every law plausible at widths 1-6 that the rewriter proves is kernel-checked at each
/// width. (B) Every law equal at width 4 but false at some width `w` in 1..=6 must be refused at `w` (no proof, or a proof
/// the kernel rejects). Prints counts; panics on a failed check or an accepted false law.
#[test]
#[ignore]
pub fn soundness_sweep() {
    tatic::kernel::scoped(|| {
        let _banner = MachineBanner::start("SWEEP");
        let family = env_var("SWEEP_FAMILY").unwrap_or("mul");
        let widths: Vec<usize> = env_var("SWEEP_WIDTHS").unwrap_or("3,4").split(',').map(|w| w.parse().unwrap()).collect();
        let kv = family_vars(&family);
        let laws = family_laws(&family, &env_or::<usize>, 4, kv, env_or("MULMINER_MAX", 7) as u32);
        let capped = |t: &Term, w: usize| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap()) && w > 0;
        let (mut checked, mut unproved, mut refused, mut false_laws) = (0usize, 0usize, 0usize, 0usize);
        let t0 = Instant::now();
        for (name, t1, t2) in &laws {
            if capped(t1, 1) || capped(t2, 1) {
                continue;
            }
            let true_everywhere = t1.is_law(t2, kv);
            if true_everywhere {
                for &w in &widths {
                    match rewrite_law(w, kv, t1, t2) {
                        Some((p, s)) => {
                            if let Err(m) = holds(&p, &s) {
                                panic!("kernel rejected the proof of {name} at width {w}: {}", m.chars().take(300).collect::<String>());
                            }
                            checked += 1;
                        }
                        None => unproved += 1,
                    }
                }
            } else {
                false_laws += 1;
                for w in (1..=6).filter(|w| !t1.plausibly_equals(t2, *w, kv)) {
                    if let Some((p, s)) = rewrite_law(w, kv, t1, t2) {
                        assert!(holds(&p, &s).is_err(), "FALSE law accepted: {name} at width {w}");
                    }
                    refused += 1;
                }
            }
        }
        println!("SWEEP {family}: {} laws; true: {checked} proofs kernel-checked at widths {widths:?}, {unproved} unproved; false at some width: {false_laws} laws, {refused} (law, width) pairs refused; {:?}", laws.len(), t0.elapsed());
    })
}

/// Scaling probe (search note section 65): a sample of each family's laws (`SWEEP_SAMPLE`, default 30, evenly spaced among the
/// true laws within the carry cap) proved by `rewrite_law` and kernel-checked at each of `SWEEP_WIDTHS` (default `4,8,16,32`),
/// then every promoted rule via `prove_rule`. Per width: proofs, unproved, build and check seconds (sum and max), flushed as it goes.
#[test]
#[ignore]
pub fn scaling_sweep() {
    // SWEEP_SCOPE=law: one intern scope per law instead of one for the sweep (separates table size from per-node cost)
    let per_law = env_var("SWEEP_SCOPE").is_some_and(|v| v == "law");
    let body = || {
        let _banner = MachineBanner::start("SCALE");
        let family = env_var("SWEEP_FAMILY").unwrap_or("mul");
        let widths: Vec<usize> = env_var("SWEEP_WIDTHS").unwrap_or("4,8,16,32").split(',').map(|w| w.parse().unwrap()).collect();
        let kv = family_vars(&family);
        if let Some(f) = env_var("SWEEP_RULES") {
            let rules = parse_rules(&std::fs::read_to_string(f).unwrap());
            set_extra_rules(rules);
        }
        let all = family_laws(&family, &env_or::<usize>, 4, kv, env_or("MULMINER_MAX", 7) as u32);
        let ok: Vec<&(String, Term, Term)> = all
            .iter()
            .filter(|(_, a, b)| a.is_law(b, kv) && ![a, b].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap())))
            .collect();
        let sample = env_or("SWEEP_SAMPLE", 30).min(ok.len()).max(1);
        let picked: Vec<&&(String, Term, Term)> = (0..sample).map(|i| &ok[i * ok.len() / sample]).collect();
        for &w in &widths {
            let (mut proved, mut none, mut build, mut check_t, mut worst) = (0, 0, 0f64, 0f64, (0f64, String::new()));
            let mut dags: Vec<usize> = vec![];
            let fb0 = MACHINE_FALLBACKS.with(|c| c.get());
            for law in &picked {
                let (name, t1, t2) = &***law;
                let mut body = || {
                    RULE_BUDGET.with(|b| b.set(200));
                    let t = Instant::now();
                    let r = rewrite_law(w, kv, t1, t2);
                    let b = t.elapsed().as_secs_f64();
                    build += b;
                    match r {
                        Some((p, s)) => {
                            dags.push(tatic::kernel::term_sizes(&p).0 as usize);
                            let t = Instant::now();
                            ck(name, &p, &s);
                            let c = t.elapsed().as_secs_f64();
                            check_t += c;
                            proved += 1;
                            if b + c > worst.0 {
                                worst = (b + c, name.clone());
                            }
                        }
                        None => none += 1,
                    }
                };
                if per_law { tatic::kernel::scoped(body) } else { body() }
            }
            println!("SCALE {family} n={w}: {proved} proved, {none} unproved of {}; build {build:.1}s, check {check_t:.1}s, slowest {:.2}s ({}), {} machine proofs", picked.len(), worst.0, worst.1, MACHINE_FALLBACKS.with(|c| c.get()) - fb0);
            dags.sort();
            if let Some(m) = dags.get(dags.len() / 2) {
                println!("SCALE {family} n={w}: proof dag nodes: median {m}, max {}, total {}", dags[dags.len() - 1], dags.iter().sum::<usize>());
            }
        }
        let t = Instant::now();
        for &w in widths.iter().filter(|_| env_var("SWEEP_RULES").is_none()) {
            let t = Instant::now();
            for (l, r) in promoted_rules() {
                assert!(prove_rule(w, l.max_var().max(r.max_var()) + 1, l, r).is_some(), "promoted rule not provable at width {w}");
            }
            println!("SCALE promoted rules n={w}: {:.1}s for {}", t.elapsed().as_secs_f64(), promoted_rules().len());
        }
        let _ = t;
    };
    if !per_law { tatic::kernel::scoped(body) } else { body() }
}

/// The pool of the `add3` family: terms over `x`, `y`, `z` with at most one sum or difference above depth-1 terms.
///
/// `deep`: also the sums and differences of two depth-1 terms built from `add`, `sub` and `xor` (about 2^15 more terms).
pub fn add3_pool(deep: bool) -> Vec<Term> {
    let leaves = leaves3();
    let d1 = depth1(&[ADD, AND, OR, XOR, SUB], false);
    let mut p = d1.clone();
    // one more level: a sum or difference of a depth-1 term and a leaf
    for o in [ADD, SUB] {
        for a in &d1 {
            for b in &leaves {
                p.push(mk(o, a, b));
            }
        }
    }
    if deep {
        let arith: Vec<Term> = d1.iter().filter(|t| matches!(*t.node(), Node::Op(ADD | XOR | SUB, ..))).cloned().collect();
        for o in [ADD, SUB] {
            for a in &arith {
                for b in &arith {
                    p.push(mk(o, a, b));
                }
            }
        }
    }
    p
}

/// The three-variable families, by name. `pool3` is the single place that maps one to its term pool; everything else (law selection,
/// `family_vars`, the shape-halves test) follows from it.
pub const THREE_VAR_FAMILIES: [&str; 7] = ["add3", "mix3", "sbo3", "cmp3", "cmp3d", "u3", "u3w"];

/// The term pool of a three-variable family (`None` for any other family). add3: the add/sub/xor reassociation family (`RULEMINER_DEEP3=1`
/// for the deeper pool); mix3: bit-trick laws, arithmetic and bitwise operators and `shl1` mixed (section 73); sbo3: add, sub, and, or only,
/// a leaf on either side at every level; cmp3: `lt` of two small add/sub/shl1 terms (laws about comparisons); cmp3d: cmp3 with
/// reassociation redexes inside the comparison.
pub fn pool3(family: &str, env: &dyn Fn(&str, usize) -> usize) -> Option<Vec<Term>> {
    let pool: Vec<Term> = match family {
        "add3" => add3_pool(env("RULEMINER_DEEP3", 0) == 1),
        "mix3" => depth2_pool(&[ADD, AND, OR, XOR, SUB], true, &[ADD]),
        "sbo3" => depth2_pool(&[ADD, SUB, AND, OR], false, &[ADD, SUB]),
        "cmp3" => cmp3_pool(false),
        "cmp3d" => cmp3_pool(true),
        // u3: the union of the add3, sbo3 and cmp3d pools (a mixed stream for mining one library over several families)
        "u3" => ["add3", "sbo3", "cmp3d"].iter().flat_map(|f| pool3(f, env).unwrap()).collect(),
        _ => return None,
    };
    // each term once: the builders make some small terms at more than one depth, and a repeat pairs a term with its own copy (a
    // trivial law) or repeats a law (docs/tier-cycle.md, pool duplicates; law sequences before this dedup differ)
    let mut seen = hashbrown::HashSet::new();
    Some(pool.into_iter().filter(|t| seen.insert(*t)).collect())
}

/// `show_cmp` is the order of the `show()` text, on every pair of a pool's first 300 terms (which include constants and variables).
#[test]
pub fn show_cmp_is_the_text_order() {
    let pool = pool3("cmp3d", &|k, d| if k == "RULEMINER_DEEP3" { 1 } else { d }).unwrap();
    let ts: Vec<&Term> = pool.iter().take(300).chain([&Term::ZERO, &Term::ONES]).collect();
    for a in &ts {
        for b in &ts {
            assert_eq!(a.show_cmp(b), a.show().cmp(&b.show()), "{} vs {}", a.show(), b.show());
        }
    }
}

/// No three-variable pool repeats a term (a repeat makes trivial and repeated laws).
#[test]
pub fn pools_have_no_repeated_terms() {
    for f in ["add3", "mix3", "sbo3", "cmp3", "cmp3d", "u3"] {
        let pool = pool3(f, &|k, d| if k == "RULEMINER_DEEP3" { 1 } else { d }).unwrap();
        let distinct: HashSet<&Term> = pool.iter().collect();
        assert_eq!(distinct.len(), pool.len(), "{f}");
    }
}

/// The law generator's source (docs/superpowers/specs/2026-10-17-law-generator-design.md): `grammar_sample`'s terms
/// grouped with the pool by their width-4 values (`pool_conjectures`). Its laws are the pairs with a grown side that use all
/// three variables and have no padded grown side, shuffled by `salt`. Pools are closed under renaming variables, so no law
/// here is a stream law or shares a stream law's skeleton.
pub fn grammar_laws(family: &str, deep3: usize, salt: usize) -> Vec<(Term, Term)> {
    let Some((pool, sample)) = grammar_sample(family, deep3, salt) else { return vec![] };
    let in_pool: HashSet<Term> = pool.iter().cloned().collect();
    let padded: HashSet<Term> = sample.iter().filter(|s| s.1).map(|s| s.0).collect();
    // the pool first, so a group's first member (each law's left side) is a pool term where the group has one
    let laws = pool_conjectures(pool.iter().cloned().chain(sample.iter().map(|s| s.0)), 4, 3, 0)
        .into_iter()
        .filter(|(a, b)| !in_pool.contains(a) || !in_pool.contains(b))
        .filter(|(a, b)| (0..3).all(|v| a.has_var(v) || b.has_var(v)))
        .filter(|(a, b)| !padded.contains(a) && !padded.contains(b))
        .collect();
    shuffled(laws, salt)
}

/// The generator's term budget: about this many grown terms are sampled per family (the value every probe run used).
pub const GEN_TERMS: usize = 20000;

/// A three-variable family's pool and the generator's sample of grown terms: the pool with one leaf of a pool term grown
/// into a depth-1 term over the pool's own operators, about `GEN_TERMS` of those drawn by a hash of `salt`, each once and
/// with whether its grown leaf was padding (grew into a term equal to a leaf, such as `sub(y, y)`; the first way it was
/// grown). `None` for a family with no pool.
pub fn grammar_sample(family: &str, deep3: usize, salt: usize) -> Option<(Vec<Term>, Vec<(Term, bool)>)> {
    let env = |k: &str, d: usize| if k == "RULEMINER_DEEP3" { deep3 } else { d };
    let pool = pool3(family, &env)?;
    let in_pool: HashSet<Term> = pool.iter().cloned().collect();
    // the operators the pool uses below a comparison (an `lt` result is one bit wide and is never an argument)
    fn ops_of(t: Term, out: &mut std::collections::BTreeSet<usize>) {
        if let Node::Op(o, a, b) = *t.node() {
            if o != LT {
                out.insert(o);
            }
            ops_of(a, out);
            ops_of(b, out);
        }
    }
    let mut ops = std::collections::BTreeSet::new();
    pool.iter().for_each(|t| ops_of(*t, &mut ops));
    let leaves = leaves3();
    let grow: Vec<Term> = ops
        .iter()
        .flat_map(|&o| if o == SHL1 { leaves.iter().map(|a| mk(SHL1, a, &Term::ZERO)).collect::<Vec<_>>() } else { leaves.iter().flat_map(|a| leaves.iter().map(move |b| mk(o, a, b))).collect() })
        .collect();
    // the leaf positions of a term (`shl1`'s second argument is not one), and the term with leaf `k` replaced by `g`
    fn leaf_count(t: Term) -> usize {
        match *t.node() {
            Node::Op(SHL1, a, _) => leaf_count(a),
            Node::Op(_, a, b) => leaf_count(a) + leaf_count(b),
            _ => 1,
        }
    }
    fn replaced(t: Term, k: &mut Option<usize>, g: Term) -> Term {
        match *t.node() {
            Node::Op(SHL1, a, b) => Term::op(SHL1, replaced(a, k, g), b),
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
    let total: usize = pool.iter().map(|t| leaf_count(*t)).sum::<usize>() * grow.len();
    let mix = tatic::rng::mix64;
    let mut memo = ValueMemo::exhaustive(4, 3);
    let leaf_values: Vec<Vec<u8>> = leaves.iter().map(|l| memo.values(l).to_vec()).collect();
    let padding: Vec<bool> = grow.iter().map(|g| leaf_values.contains(&memo.values(g).to_vec())).collect();
    // each grown term, and whether its grown leaf was padding (the first way it was grown)
    let (mut sample, mut seen) = (vec![], HashSet::new());
    let mut i = 0u64;
    for t in &pool {
        for p in 0..leaf_count(*t) {
            for (gi, g) in grow.iter().enumerate() {
                i += 1;
                if (mix(i ^ mix(salt as u64)) % total as u64) < GEN_TERMS as u64 {
                    let w = replaced(*t, &mut Some(p), *g);
                    if !in_pool.contains(&w) && seen.insert(w) {
                        sample.push((w, padding[gi]));
                    }
                }
            }
        }
    }
    Some((pool, sample))
}

/// The grammar source's laws hold at width 4, each has a side outside the family's pool (so none is a stream law or shares
/// a stream law's skeleton), uses all three variables, and the same salt gives the same laws.
#[test]
pub fn grammar_laws_lie_outside_the_pool() {
    let env = |k: &str, d: usize| if k == "RULEMINER_DEEP3" { 1 } else { d };
    for f in ["add3", "sbo3", "cmp3d"] {
        let pool: HashSet<Term> = pool3(f, &env).unwrap().into_iter().collect();
        let laws = grammar_laws(f, 1, 1);
        assert!(laws.len() > 100, "{f}: {} laws", laws.len());
        assert!(laws == grammar_laws(f, 1, 1), "{f}: same salt, other laws");
        println!("{f}: {} laws, e.g. {}", laws.len(), laws.iter().take(3).map(|(a, b)| format!("{} = {}", a.show(), b.show())).collect::<Vec<_>>().join("; "));
        let mut memo = ValueMemo::exhaustive(4, 3);
        for (a, b) in &laws {
            assert!(!pool.contains(a) || !pool.contains(b), "{f}: {} = {} is a stream law", a.show(), b.show());
            assert!((0..3).all(|v| a.has_var(v) || b.has_var(v)), "{f}: {} = {}", a.show(), b.show());
            assert_eq!(memo.values(a).to_vec(), memo.values(b).to_vec(), "{f}: {} = {}", a.show(), b.show());
        }
    }
}

/// The generator takes no padding law: no side of its laws is a sample term whose grown leaf was padding, and the sample
/// has such terms (so the check bites).
#[test]
pub fn grammar_laws_have_no_padding() {
    for f in ["add3", "cmp3d"] {
        let (_, sample) = grammar_sample(f, 1, 1).unwrap();
        let padded: HashSet<Term> = sample.iter().filter(|s| s.1).map(|s| s.0).collect();
        assert!(!padded.is_empty(), "{f}: no padding term in the sample");
        let laws = grammar_laws(f, 1, 1);
        let bad = laws.iter().filter(|(a, b)| padded.contains(a) || padded.contains(b)).count();
        assert_eq!(bad, 0, "{f}: {bad} of {} laws have a padded side", laws.len());
    }
}

/// The width-4 value classes of the leaves and the two-leaf terms (the law generator's twin filter,
/// docs/superpowers/specs/2026-10-17-law-generator-design.md §1, `scripts/twin_wide.py`'s `REP`).
pub struct ClassReps {
    memo: ValueMemo<u8>,
    /// a class's values to its representative
    rep: hashbrown::HashMap<Vec<u8>, Term>,
    /// two-leaf nodes already looked up
    done: hashbrown::HashMap<Term, Term>,
}

impl ClassReps {
    pub fn new() -> ClassReps {
        let mut memo = ValueMemo::exhaustive(4, 3);
        let leaves = leaves3();
        let mut two = vec![];
        for o in [ADD, SUB, XOR, AND, OR] {
            for a in &leaves {
                for b in &leaves {
                    two.push(mk(o, a, b));
                }
            }
        }
        two.extend(leaves.iter().map(|a| mk(SHL1, a, &Term::ZERO)));
        two.sort_by_cached_key(|t| {
            let s = t.show();
            (s.len(), s)
        });
        let mut rep = hashbrown::HashMap::new();
        // a leaf where the class has one (the first in x, y, z, 0, -1), else the least two-leaf term by (length, text)
        for t in leaves.iter().chain(&two) {
            rep.entry(memo.values(t).to_vec()).or_insert(*t);
        }
        ClassReps { memo, rep, done: Default::default() }
    }

    /// `t` with every node over two leaves (an `lt` aside), bottom-up, replaced by its class's representative.
    pub fn normalize(&mut self, t: Term) -> Term {
        let Node::Op(o, a, b) = *t.node() else { return t };
        let (a, b) = (self.normalize(a), self.normalize(b));
        let n = Term::op(o, a, b);
        let leaf = |t: Term| !matches!(t.node(), Node::Op(..));
        if o == LT || !leaf(a) || !leaf(b) {
            return n;
        }
        if let Some(r) = self.done.get(&n) {
            return *r;
        }
        let r = self.rep.get(self.memo.values(&n)).copied().unwrap_or(n);
        self.done.insert(n, r);
        r
    }

    /// A law's twin key: the least `a = b` text, over the six renamings of x, y, z and both side orders, of the law renamed
    /// then normalized (renaming first, since a representative is not preserved by renaming); `None` if the law's sides
    /// normalize to one term.
    pub fn key(&mut self, a: &Term, b: &Term) -> Option<String> {
        if self.normalize(*a) == self.normalize(*b) {
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
                let s = format!("{} = {}", self.normalize(renamed(*l, p)).show(), self.normalize(renamed(*r, p)).show());
                if best.as_ref().is_none_or(|k| s < *k) {
                    best = Some(s);
                }
            }
        }
        best
    }
}

/// Normalization maps padding to its leaf, puts value-equal two-leaf nodes in one class, leaves nodes over a non-leaf and
/// `lt` alone, and the key is the same for two laws that differ by renaming variables.
#[test]
pub fn normalize_maps_two_leaf_nodes_to_their_class() {
    let mut c = ClassReps::new();
    let mut n = |s: &str| c.normalize(parse_term(s)).show();
    assert_eq!(n("sub(y, y)"), "0");
    assert_eq!(n("add(x, 0)"), "x");
    assert_eq!(n("xor(x, -1)"), n("sub(-1, x)"));
    let r = n("or(z, x)");
    assert_eq!(n("add(or(z, x), sub(sub(y, y), 0))"), format!("add({r}, 0)"), "the outer add is over a non-leaf");
    assert_eq!(n("lt(x, x)"), "lt(x, x)");
    let p = parse_term;
    let swap = c.key(&p("sub(or(y, x), y)"), &p("and(y, z)"));
    assert_eq!(c.key(&p("sub(or(x, y), x)"), &p("and(x, z)")), swap, "renaming x and y");
    assert!(swap.is_some());
    assert_eq!(c.key(&p("sub(y, y)"), &p("and(x, 0)")), None, "both sides normalize to 0");
}

/// On the probe's fixture (salt 1 of `-gen-cost`'s pad arm, cmp3d: mine 0's extras of phases 1-3 against the served laws of
/// phases 1-3), the extras whose key is a served law's key are as many as `scripts/twin_wide.py` counts (`class`, trivial
/// laws not counted).
#[test]
pub fn normalize_finds_the_probes_twins() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/runs/2026-10-17/fixtures/pad_1");
    let laws = |p: std::path::PathBuf| -> Vec<(Term, Term)> {
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display())).lines().filter_map(|l| parse_law(l, 3)).collect()
    };
    let loops: Vec<std::path::PathBuf> = (1..=3).map(|p| dir.join(format!("cold_cmp3d_{p}_none"))).collect();
    let served: Vec<(Term, Term)> = loops.iter().flat_map(|l| [0, 100, 200].map(|s| l.join(format!("laws_serve_{s}.txt")))).flat_map(laws).collect();
    let extras: Vec<(Term, Term)> = loops.iter().flat_map(|l| laws(l.join("laws_extra_0.txt"))).collect();
    assert_eq!((served.len(), extras.len()), (900, 1050));
    let mut c = ClassReps::new();
    let keys: HashSet<String> = served.iter().filter_map(|(a, b)| c.key(a, b)).collect();
    let twins = extras.iter().filter(|(a, b)| c.key(a, b).is_some_and(|k| keys.contains(&k))).count();
    assert_eq!(twins, 502, "twin_wide.py counts 502; find out which of the two is wrong before going on");
}

/// Variables per law of a family: the three-variable families against the two-variable rest.
pub fn family_vars(family: &str) -> usize {
    if THREE_VAR_FAMILIES.contains(&family) { 3 } else { 2 }
}

/// Terms of the `cmp3` family: `lt` of two arithmetic terms (add, sub, `shl1` over three variables, depth one: an operator over two
/// leaves, `shl1` of a leaf, or a leaf), so each law is a statement about a comparison. `lt` is never nested under arithmetic: the
/// encoding types its result differently.
pub fn cmp3_pool(deep: bool) -> Vec<Term> {
    let op = mk;
    let d1 = depth1(&[ADD, SUB], true);
    if deep {
        // cmp3d: the right argument may also be a sum or difference of a variable-only depth-1 term and a variable, so a comparison
        // can contain a reassociation redex (cmp3d mixes the comparison and the add/sub structures)
        let vars: Vec<Term> = (0..3).map(Term::v).collect();
        let mut v1 = vars.clone();
        for o in [ADD, SUB] {
            for a in &vars {
                for b in &vars {
                    v1.push(op(o, a, b));
                }
            }
        }
        let mut e = d1.clone();
        for o in [ADD, SUB] {
            for a in &v1 {
                for b in &vars {
                    e.push(op(o, a, b));
                    e.push(op(o, b, a));
                }
            }
        }
        return d1.iter().flat_map(|a| e.iter().map(|b| op(LT, a, b)).collect::<Vec<_>>()).collect();
    }
    d1.iter().flat_map(|a| d1.iter().map(|b| op(LT, a, b)).collect::<Vec<_>>()).collect()
}

/// Terms of the depth-2 families (sbo3, mix3): the depth-1 terms, each of `ops` over a depth-1 term and a leaf (both orders), `shl1` of
/// each depth-1 term when `shl`, and each of `sums` over two depth-1 terms.
pub fn depth2_pool(ops: &[usize], shl: bool, sums: &[usize]) -> Vec<Term> {
    let leaves = leaves3();
    let d1 = depth1(ops, shl);
    let mut p = d1.clone();
    for &o in ops {
        for a in &d1 {
            for b in &leaves {
                p.push(mk(o, a, b));
                p.push(mk(o, b, a));
            }
        }
    }
    if shl {
        p.extend(d1.iter().map(|a| mk(SHL1, a, &Term::ZERO)));
    }
    for &o in sums {
        for a in &d1 {
            for b in &d1 {
                p.push(mk(o, a, b));
            }
        }
    }
    p
}

/// `x`, `y`, `z`, `0` and `-1`.
fn leaves3() -> Vec<Term> {
    (0..3).map(Term::v).chain([Term::ZERO, Term::ONES]).collect()
}

fn mk(o: usize, a: &Term, b: &Term) -> Term {
    Term::op(o, *a, *b)
}

/// The depth-1 terms: the leaves, each of `ops` over two leaves, and, with `shl`, `shl1` of a leaf.
fn depth1(ops: &[usize], shl: bool) -> Vec<Term> {
    let leaves = leaves3();
    let mut d1 = leaves.clone();
    for &o in ops {
        for a in &leaves {
            for b in &leaves {
                d1.push(mk(o, a, b));
            }
        }
    }
    if shl {
        d1.extend(leaves.iter().map(|a| mk(SHL1, a, &Term::ZERO)));
    }
    d1
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
    tatic::kernel::scoped(|| {
        let rules: Vec<(Term, Term)> = parse_rules(&std::fs::read_to_string(env_var("NF_RULES").unwrap_or_default()).unwrap_or_default());
        set_extra_rules(rules);
        TRACE_RULES.get(Default::default).store(env_flag("NF_TRACE", false), std::sync::atomic::Ordering::Relaxed);
        RULE_BUDGET.with(|b| b.set(200));
        let (n, k) = (4, 3);
        for line in std::fs::read_to_string(env_var("NF_LAWS").unwrap()).unwrap().lines().filter(|l| l.contains(" = ")) {
            let (a, b) = line.split_once(" = ").unwrap();
            let (a, b) = (parse_term(a), parse_term(b));
            // each side with its own budget, as in `rewrite_law`; `steps` is what each used (200 or more: it used the budget up)
            let side = |t: &Term| {
                RULE_BUDGET.with(|c| c.set(200));
                (rewrite(t, n, k).0, 200 - RULE_BUDGET.with(|c| c.get()))
            };
            let ((na, sa), (nb, sb)) = (side(&a), side(&b));
            let carries = |t: &Term| Machine::parse(t).map_or(0, |m| m.carries());
            println!("NF {} | {} {} carries {}/{} steps {sa}/{sb}", na.show(), nb.show(), if na == nb { "SAME" } else { "DIFF" }, carries(&na), carries(&nb));
        }
    })
}

/// The `shrnot` rule and the laws it closes: a shift of a bitwise not distributes over xor, so both sides reach the same
/// xor of shifted atoms without a whole-term machine proof.
#[test]
pub fn shrnot_rule_is_provable_and_closes_the_shr_not_laws() {
    tatic::kernel::scoped(|| {
        for n in [4usize, 8] {
            let (l, r) = shrnot_rule();
            let (p, s) = prove_rule(n, 1, &l, &r).expect("shrnot");
            ck(&format!("shrnot n={n}"), &p, &s);
        }
        for (a, b) in [
            ("shr1(sub(-1, xor(x, y)), 0)", "xor(shr1(y, 0), xor(shr1(-1, 0), shr1(x, 0)))"),
            ("shr1(xor(xor(x, y), -1), 0)", "shr1(xor(sub(-1, x), y), 0)"),
        ] {
            let before = MACHINE_FALLBACKS.with(|c| c.get());
            let (p, s) = rewrite_law(4, 2, &parse_term(a), &parse_term(b)).unwrap_or_else(|| panic!("{a} = {b}"));
            ck(a, &p, &s);
            assert_eq!(MACHINE_FALLBACKS.with(|c| c.get()), before, "{a} = {b} needed a machine proof");
        }
    })
}

/// The setup of the rule-set check tests: the `CHECK_RULES` installed as extra rules (with their preferences), `CHECK_FAMILY`'s
/// variable count, and the laws of the family (sized by the `RULEMINER_*` vars, or the `lhs = rhs` lines of `CHECK_LAWFILE`, as
/// the driver passes them) that are plausible at widths 1-6.
fn check_laws() -> (Vec<(Term, Term)>, usize, Vec<(String, Term, Term)>) {
    let family = env_var("CHECK_FAMILY").unwrap_or("add3");
    let text = std::fs::read_to_string(env_var("CHECK_RULES").unwrap()).unwrap();
    let rules = parse_rules(&text);
    let kv = family_vars(&family);
    let laws = match env_var("CHECK_LAWFILE") {
        Some(f) => read_named_laws(&f),
        None => family_laws(&family, &env_or::<usize>, 4, kv, 7),
    };
    let laws = laws.into_iter().filter(|(_, t1, t2)| t1.is_law(t2, kv)).collect();
    set_extra_rules(rules.clone());
    set_rule_prefs(parse_prefs(&text));
    (rules, kv, laws)
}

/// Kernel check of a rule set (search note section 75): every law of `CHECK_FAMILY` (sized by the `RULEMINER_*` vars, as in
/// `rule_miner`) that `rewrite_law` proves under the built-in rules (less `ABLATE`) plus the rules in `CHECK_RULES` is
/// checked by the kernel at width 4; prints how many were proved, how many without a whole-term machine proof, and per law
/// `MACHINE <count> <law>` for the others and `EXHAUSTED <law>` for one that used up the step budget.
#[test]
#[ignore]
pub fn rule_set_kernel_check() {
    let _save = lemma_cache::Save;
    tatic::kernel::scoped(|| {
        let (_, kv, laws) = check_laws();
        // CHECK_FAST=1: count only (machine fallbacks are counted without building their proofs, nothing is kernel-checked, no NFSAME pass);
        // the CHECKED line and so M are unchanged, for exploration (the miner's RULEMINER_FAST, applied to serving)
        let fast = env_flag("CHECK_FAST", false);
        SCORE_ONLY.with(|s| s.set(fast));
        if env_flag("RULE_CONFLICTS", false) {
            *RULE_CONFLICTS.get(Default::default).lock().unwrap() = Some(Default::default());
        }
        let (mut proved, mut free, mut none, mut exhausted, mut joined) = (0, 0, 0, 0, 0);
        let (cost0, met) = (JoinCost::now(), || JoinCost::now().met);
        for (name, t1, t2) in &laws {
            RULE_BUDGET.with(|b| b.set(200));
            let (before, met0) = (MACHINE_FALLBACKS.with(|c| c.get()), met());
            let r = rewrite_plan(4, kv, t1, t2);
            // a law that used up the step budget: a rewrite cycle, or rules that grow (docs/tier-cycle.md, "A rewrite cycle")
            if RULE_BUDGET.with(|b| b.get()) <= 0 {
                exhausted += 1;
                println!("EXHAUSTED {name}");
            }
            match r {
                Some(plan) => {
                    if !fast {
                        let (p, s) = law_proof(4, kv, t1, t2, &plan);
                        ck(name, &p, &s);
                    }
                    proved += 1;
                    let machine = MACHINE_FALLBACKS.with(|c| c.get()) - before;
                    free += (machine == 0) as u32;
                    joined += (machine == 0 && met() > met0) as u32;
                    if machine > 0 {
                        println!("MACHINE {machine} {name}");
                    }
                }
                None => none += 1,
            }
        }
        println!("CHECKED {proved} laws kernel-checked ({free} with no whole-term machine proof), {none} not proved, {exhausted} used up the rule budget");
        let mut cost = JoinCost::default();
        cost.add_since(cost0);
        println!("JOINED {joined} of them by the join, {} searches reaching {} terms", cost.searches, cost.reached);
        for (key, v) in [("proved", proved), ("free", free), ("none", none), ("exhausted", exhausted), ("joined", joined)].map(|(k, v)| (k, u64::from(v))).into_iter().chain([("reached", cost.reached)]) {
            crate::task::result(key, v);
        }
        print_rule_conflicts();
        if fast {
            return;
        }
        // confluence on this law set: both sides of a law reach the same normal form (the check above counts machine-free proofs, which can also come from a middle term)
        let (mut same, mut total) = (0, 0);
        for (_, t1, t2) in &laws {
            RULE_BUDGET.with(|b| b.set(200));
            let n1 = rewrite(t1, 4, kv).0;
            RULE_BUDGET.with(|b| b.set(200));
            let n2 = rewrite(t2, 4, kv).0;
            total += 1;
            same += (n1 == n2) as u32;
        }
        println!("NFSAME {same} of {total} laws have equal normal forms on both sides");
    });
}

/// Where the kernel's work goes under a rule set: like `rule_set_kernel_check` (same `CHECK_FAMILY`, `CHECK_RULES`, `RULEMINER_*` vars), but
/// reports, for the laws proved by rules alone ("rules"), by rules and the join with no whole-term machine proof ("joined"), and
/// for those that needed one ("machine"), the count, the
/// time to build the proof, the time for the kernel to check it, and its size (unique nodes / nodes per occurrence); then the same
/// for the proofs of the rules themselves, which a conversion rule or a one-time admission would pay once.
#[test]
#[ignore]
pub fn proof_cost_split() {
    use std::time::{Duration, Instant};
    tatic::kernel::scoped(|| {
        let (rules, kv, laws) = check_laws();
        #[derive(Default)]
        struct Acc { n: u32, build: Duration, check: Duration, nodes: usize, occ: u128 }
        let mut acc = [Acc::default(), Acc::default(), Acc::default()]; // [rules, joined, machine]
        let mut none = 0;
        let met = || JoinCost::now().met;
        for (name, t1, t2) in &laws {
            RULE_BUDGET.with(|b| b.set(200));
            let (before, met0) = (MACHINE_FALLBACKS.with(|c| c.get()), met());
            let t = Instant::now();
            let Some((p, s)) = rewrite_law(4, kv, t1, t2) else { none += 1; continue };
            let build = t.elapsed();
            let t = Instant::now();
            ck(name, &p, &s);
            let check = t.elapsed();
            let (nodes, occ) = tatic::kernel::term_sizes(&p);
            let a = &mut acc[if MACHINE_FALLBACKS.with(|c| c.get()) != before { 2 } else { (met() > met0) as usize }];
            (a.n, a.build, a.check, a.nodes, a.occ) = (a.n + 1, a.build + build, a.check + check, a.nodes + nodes, a.occ + occ);
        }
        let mut ra = Acc::default();
        for (l, r) in &rules {
            let k = l.max_var().max(r.max_var()) + 1;
            let t = Instant::now();
            let Some((p, ty)) = prove_rule(4, k, l, r) else { continue };
            let build = t.elapsed();
            let t = Instant::now();
            ck(&l.show(), &p, &ty);
            let check = t.elapsed();
            let (nodes, occ) = tatic::kernel::term_sizes(&p);
            (ra.n, ra.build, ra.check, ra.nodes, ra.occ) = (ra.n + 1, ra.build + build, ra.check + check, ra.nodes + nodes, ra.occ + occ);
        }
        for (what, a) in [("rules", &acc[0]), ("joined", &acc[1]), ("machine", &acc[2]), ("rule-proofs", &ra)] {
            println!("COST {what}: n={} build={:.1}ms check={:.1}ms nodes={} occurrences={}", a.n, a.build.as_secs_f64() * 1e3, a.check.as_secs_f64() * 1e3, a.nodes, a.occ);
        }
        println!("COST not-proved={none}");
    });
}

/// Each rule of the promoted sets parses, is a true law at widths 1-4, and is proved (and kernel-checked) at width 4.
#[test]
pub fn promoted_rule_sets_are_proved() {
    tatic::kernel::scoped(|| {
        for text in [include_str!("../../scripts/data/add3_mm_rules.txt"), include_str!("../../scripts/data/mix3_mm_rules.txt"), include_str!("../../scripts/data/add3_nl_rules.txt"), include_str!("../../scripts/data/mix3_nl_rules.txt")] {
            let rs: Vec<(Term, Term)> = parse_rules(text);
            assert!(rs.len() >= 7);
            for (l, r) in rs {
                let k = l.max_var().max(r.max_var()) + 1;
                assert!((1..=4).all(|w| l.plausibly_equals(&r, w, k)), "{} -> {}", l.show(), r.show());
                let (p, t) = prove_rule(4, k, &l, &r).unwrap_or_else(|| panic!("{} -> {} not provable", l.show(), r.show()));
                ck(&l.show(), &p, &t);
            }
        }
    })
}

/// Closed terms equal to 0, -1 or 1 normalize to `0`, `-1`, `sub(0, -1)` with no machine proof (by the rules and `tree_step`; a
/// constant-folding step of its own was removed as redundant).
#[test]
pub fn closed_terms_fold_to_constants() {
    tatic::kernel::scoped(|| {
        for (a, b) in [("sub(-1, add(-1, -1))", "sub(0, -1)"), ("sub(add(0, 0), -1)", "sub(0, -1)"), ("xor(-1, -1)", "0"), ("add(-1, add(-1, sub(0, -1)))", "-1")] {
            let (t1, t2) = (parse_term(a), parse_term(b));
            let before = MACHINE_FALLBACKS.with(|c| c.get());
            let (p, ty) = rewrite_law(4, 1, &t1, &t2).unwrap_or_else(|| panic!("{a} = {b} not proved"));
            ck(a, &p, &ty);
            assert_eq!(MACHINE_FALLBACKS.with(|c| c.get()), before, "{a} = {b} needed a machine proof");
        }
    })
}

// --- Proposal yield (docs/tier-cycle.md): what a proposer's samples are worth to the kernel ---

/// What the kernel makes of one proposed `lhs = rhs` line. `Cheap` laws are proved with no whole-term machine proof under the rules in
/// force; `Hard` laws needed one (or were not proved within the rewrite budget).
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum Verdict {
    Unparsed,
    Trivial,
    Refuted,
    Duplicate,
    Memorised,
    KnownCheap,
    KnownHard,
    NovelCheap,
    NovelHard,
}

/// A `Term` from `show` syntax over at most `kv` variables, or `None` for text that does not parse (`parse_term` panics on bad input).
fn try_parse(s: &str, kv: usize) -> Option<Term> {
    let t = std::panic::catch_unwind(|| parse_term(s)).ok()?;
    (0..8).all(|v| v < kv || !t.has_var(v)).then_some(t)
}

/// The kernel's cost for a true law under the installed rules: whole-term machine proofs and rule steps (of a 200-step budget) that
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

/// The `Cost` of `t1 = t2` under the rules installed by `set_extra_rules` (a 200-step budget, width 4).
pub fn law_cost(kv: usize, t1: &Term, t2: &Term) -> Cost {
    RULE_BUDGET.with(|b| b.set(200));
    let before = MACHINE_FALLBACKS.with(|c| c.get());
    let proved = rewrite_plan(4, kv, t1, t2).is_some();
    Cost { fallbacks: MACHINE_FALLBACKS.with(|c| c.get()) - before, steps: 200 - RULE_BUDGET.with(|b| b.get()), proved }
}

/// Per-proposal credit for a mined library `rules` (docs/tier-cycle.md). Each rule's held-out gain is how many more `held` laws are hard
/// without it; a proposal uses a rule when it is cheap under `rules` but hard without that rule; each rule's gain is split evenly over
/// the proposals that use it. Returns the per-rule gains, the per-rule user counts and the per-proposal credits.
pub fn proposal_credit(rules: &[(Term, Term)], kv: usize, held: &[(Term, Term)], props: &[(Term, Term)]) -> (Vec<i64>, Vec<usize>, Vec<f64>) {
    let hard = |set: &[(Term, Term)], laws: &[(Term, Term)]| -> Vec<bool> {
        set_extra_rules(set.to_vec());
        laws.iter().map(|(a, b)| law_cost(kv, a, b).hard()).collect()
    };
    let count = |v: &[bool]| v.iter().filter(|h| **h).count() as i64;
    let (held_all, props_all) = (count(&hard(rules, held)), hard(rules, props));
    let (mut gains, mut users, mut credit) = (vec![], vec![], vec![0.0; props.len()]);
    for i in 0..rules.len() {
        let without: Vec<(Term, Term)> = rules.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, r)| *r).collect();
        let gain = count(&hard(&without, held)) - held_all;
        let uses: Vec<usize> = hard(&without, props).iter().zip(&props_all).enumerate().filter(|(_, (h, h_all))| **h && !**h_all).map(|(p, _)| p).collect();
        for &p in &uses {
            credit[p] += gain as f64 / uses.len() as f64;
        }
        gains.push(gain);
        users.push(uses.len());
    }
    set_extra_rules(vec![]);
    (gains, users, credit)
}

/// Credit for the proposals in `CREDIT_LAWS` (`lhs = rhs` lines) from the library `CHECK_RULES` mined on them, against the held-out
/// window of `CHECK_FAMILY` (the `RULEMINER_*` vars: `SKIP`, `LAWS`, `SHUFFLE`). Prints a `CREDIT rule` line per rule (held-out gain,
/// users) and a `CREDIT total` line; `CREDIT_OUT` saves `credit<TAB>law` per proposal.
#[test]
#[ignore]
pub fn proposal_credit_report() {
    tatic::kernel::scoped(|| {
        let (rules, kv, laws) = check_laws();
        SCORE_ONLY.with(|s| s.set(true));
        let held: Vec<(Term, Term)> = laws.into_iter().map(|(_, a, b)| (a, b)).collect();
        let props = read_laws(&env_var("CREDIT_LAWS").unwrap());
        let (gains, users, credit) = proposal_credit(&rules, kv, &held, &props);
        for (i, (l, r)) in rules.iter().enumerate() {
            println!("CREDIT rule {} -> {}: held-out gain {}, used by {} proposals", l.show(), r.show(), gains[i], users[i]);
        }
        set_extra_rules(vec![]);
        let m0 = held.iter().filter(|(a, b)| law_cost(kv, a, b).hard()).count();
        set_extra_rules(rules.clone());
        let m1 = held.iter().filter(|(a, b)| law_cost(kv, a, b).hard()).count();
        let credited = credit.iter().filter(|c| **c != 0.0).count();
        println!(
            "CREDIT total: held-out M {m0} -> {m1} (gain {}), sum of rule gains {}, attributed {:.1}, {credited} of {} proposals credited",
            m0 as i64 - m1 as i64,
            gains.iter().sum::<i64>(),
            credit.iter().sum::<f64>(),
            props.len()
        );
        if let Some(out) = env_var("CREDIT_OUT") {
            let text: String = props.iter().zip(&credit).map(|((a, b), c)| format!("{c:.3}\t{} = {}\n", a.show(), b.show())).collect();
            std::fs::write(out, text).unwrap();
        }
    })
}

/// A rule's credit goes to the proposal that needs it, in proportion to its held-out gain.
#[test]
pub fn proposal_credit_goes_to_rule_users() {
    tatic::kernel::scoped(|| {
        SCORE_ONLY.with(|s| s.set(true));
        let law = |s: &str| s.split_once(" = ").map(|(a, b)| (parse_term(a), parse_term(b))).unwrap();
        let rules = parse_rules("lt(x, sub(x, y)) -> lt(x, y)\n");
        // the proposal and the held-out law are both closed by the rule only if the built-in rules do not already close them
        let (p, h) = (law("lt(x, sub(x, y)) = lt(x, y)"), law("lt(z, sub(z, x)) = lt(z, x)"));
        let (gains, users, credit) = proposal_credit(&rules, 3, &[h], &[p, law("add(x, y) = add(y, x)")]);
        assert_eq!(gains.len(), 1);
        assert_eq!(credit[1], 0.0, "a proposal that does not use the rule gets nothing");
        assert_eq!(credit[0], if users[0] == 1 { gains[0] as f64 } else { 0.0 });
    })
}

/// A law line `lhs = rhs` over `kv` variables, `None` when it does not parse.
pub fn parse_law(line: &str, kv: usize) -> Option<(Term, Term)> {
    let (a, b) = line.split_once(" = ")?;
    Some((try_parse(a, kv)?, try_parse(b, kv)?))
}

/// Classify proposed lines (`lhs = rhs`). `train` holds the laws the proposer was shown, `known` every law of the family (either
/// orientation); the other classes follow from parsing, the width 1-6 screen and `rewrite_law` under the
/// installed rules, which also gives each true, unmemorised law its `Cost`.
pub fn classify_proposals(lines: &[String], kv: usize, train: &HashSet<(Term, Term)>, known: &HashSet<(Term, Term)>) -> Vec<(Verdict, Option<Cost>)> {
    let mut seen: HashSet<(Term, Term)> = HashSet::new();
    lines
        .iter()
        .map(|line| {
            let Some((t1, t2)) = parse_law(line, kv) else { return (Verdict::Unparsed, None) };
            if t1 == t2 {
                return (Verdict::Trivial, None);
            }
            let (fwd, rev) = ((t1, t2), (t2, t1));
            if !t1.is_law(&t2, kv) {
                return (Verdict::Refuted, None);
            }
            if !seen.insert(fwd) || seen.contains(&rev) {
                return (Verdict::Duplicate, None);
            }
            if train.contains(&fwd) || train.contains(&rev) {
                return (Verdict::Memorised, None);
            }
            let cost = law_cost(kv, &t1, &t2);
            let verdict = match (known.contains(&fwd) || known.contains(&rev), cost.hard()) {
                (true, false) => Verdict::KnownCheap,
                (true, true) => Verdict::KnownHard,
                (false, false) => Verdict::NovelCheap,
                (false, true) => Verdict::NovelHard,
            };
            (verdict, Some(cost))
        })
        .collect()
}

use hashbrown::HashSet;

fn lcg(s: &mut u64) -> u64 {
    *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *s >> 33
}

/// A character n-gram model of `text` (context of `order` bytes), sampled into `n` lines: the stand-in proposer a language model replaces.
pub fn ngram_lines(text: &str, order: usize, n: usize, seed: u64) -> Vec<String> {
    let bytes = text.as_bytes();
    let mut table: hashbrown::HashMap<&[u8], Vec<u8>> = Default::default();
    for i in 0..bytes.len() {
        table.entry(&bytes[i.saturating_sub(order)..i]).or_default().push(bytes[i]);
    }
    let mut s = seed;
    (0..n)
        .map(|_| {
            let mut out: Vec<u8> = Vec::new();
            while out.len() < 160 {
                let ctx = &out[out.len().saturating_sub(order)..];
                // back off to shorter contexts until one was seen
                let Some(next) = (0..=ctx.len()).find_map(|k| table.get(&ctx[k..])) else { break };
                let c = next[lcg(&mut s) as usize % next.len()];
                if c == b'\n' {
                    break;
                }
                out.push(c);
            }
            String::from_utf8_lossy(&out).into_owned()
        })
        .collect()
}

/// The `lhs = rhs` lines of a file as term pairs.
pub fn read_laws(path: &str) -> Vec<(Term, Term)> {
    std::fs::read_to_string(path).unwrap().lines().filter_map(|l| l.split_once(" = ")).map(|(a, b)| (parse_term(a), parse_term(b))).collect()
}

/// `read_laws` with each law named as `family_laws` names it.
pub fn read_named_laws(path: &str) -> Vec<(String, Term, Term)> {
    read_laws(path).into_iter().map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b)).collect()
}

/// `t` with variable `v` replaced by `r`.
fn subst(t: &Term, v: usize, r: &Term) -> Term {
    match *t.node() {
        Node::V(i) if i == v => *r,
        Node::Op(o, a, b) => Term::op(o, subst(&a, v, r), subst(&b, v, r)),
        _ => *t,
    }
}

fn nodes(t: &Term) -> usize {
    match *t.node() {
        Node::Op(_, a, b) => 1 + nodes(&a) + nodes(&b),
        _ => 1,
    }
}

/// `t` with its `k`-th node in preorder replaced by `r` (`k` counts down, `None` once replaced).
fn replace_node(t: &Term, k: &mut Option<usize>, r: &Term) -> Term {
    match *k {
        Some(0) => {
            *k = None;
            return *r;
        }
        Some(j) => *k = Some(j - 1),
        None => return *t,
    }
    match *t.node() {
        Node::Op(o, a, b) => {
            let a2 = replace_node(&a, k, r);
            Term::op(o, a2, replace_node(&b, k, r))
        }
        _ => *t,
    }
}

fn ops_in(t: &Term, out: &mut std::collections::BTreeSet<usize>) {
    if let Node::Op(o, a, b) = *t.node() {
        out.insert(o);
        ops_in(&a, out);
        ops_in(&b, out);
    }
}

/// Mutants of the seed laws, `n` of them, by `kind`: `subst` (a variable replaced by a small term on both sides) and `wrap` (both sides
/// put under the same operator with a small term) are true by construction; `edit` (one node of one side replaced by a small term) mostly
/// is not; `mix` cycles through the three. Small terms are a leaf or one operator of the seeds over leaves; `lt` stays at the root.
pub fn mutate_laws(seeds: &[(Term, Term)], kv: usize, kind: &str, n: usize, seed: u64) -> Vec<String> {
    let mut ops = std::collections::BTreeSet::new();
    for (a, b) in seeds {
        ops_in(a, &mut ops);
        ops_in(b, &mut ops);
    }
    let inner: Vec<usize> = ops.iter().copied().filter(|&o| o != LT).collect();
    let mut s = seed;
    let mut pick = |m: usize| lcg(&mut s) as usize % m.max(1);
    let mut out = vec![];
    for i in 0..n {
        let leaf = |p: &mut dyn FnMut(usize) -> usize| match p(kv + 2) {
            j if j < kv => Term::v(j),
            j if j == kv => Term::ZERO,
            _ => Term::ONES,
        };
        let small = |p: &mut dyn FnMut(usize) -> usize| {
            if inner.is_empty() || p(2) == 0 {
                leaf(p)
            } else {
                let o = inner[p(inner.len())];
                Term::op(o, leaf(p), leaf(p))
            }
        };
        let (a, b) = &seeds[pick(seeds.len())];
        let k = match kind {
            "mix" => ["subst", "wrap", "edit"][i % 3],
            k => k,
        };
        let (a2, b2) = match k {
            "subst" => {
                let v = pick(kv);
                let r = small(&mut pick);
                (subst(a, v, &r), subst(b, v, &r))
            }
            "wrap" => {
                let rooted = matches!(*a.node(), Node::Op(LT, ..)) || matches!(*b.node(), Node::Op(LT, ..));
                let o = if rooted || inner.is_empty() { continue } else { inner[pick(inner.len())] };
                let (r, left) = (small(&mut pick), pick(2) == 0);
                let w = |t: &Term| if left { Term::op(o, *t, r) } else { Term::op(o, r, *t) };
                (w(a), w(b))
            }
            "edit" => {
                let r = small(&mut pick);
                let side = pick(2);
                let t = if side == 0 { a } else { b };
                // the root of an `lt` side stays (`lt` only at the root); other nodes may be replaced
                let lo = matches!(*t.node(), Node::Op(LT, ..)) as usize;
                let mut k = Some(lo + pick(nodes(t) - lo));
                let e = replace_node(t, &mut k, &r);
                if side == 0 { (e, *b) } else { (*a, e) }
            }
            _ => panic!("MUTATE_KIND is subst, wrap, edit or mix"),
        };
        out.push(format!("{} = {}", a2.show(), b2.show()));
    }
    out
}

/// Mutants keep `lt` at the root, and the true-by-construction kinds stay laws.
#[test]
pub fn mutants_are_well_formed() {
    let seeds: Vec<(Term, Term)> = ["lt(x, sub(x, y)) = lt(x, y)", "sub(x, add(y, z)) = sub(sub(x, y), z)"]
        .iter()
        .map(|l| l.split_once(" = ").map(|(a, b)| (parse_term(a), parse_term(b))).unwrap())
        .collect();
    let lt_inside = |t: &Term| -> bool {
        fn any_lt(t: &Term) -> bool {
            matches!(*t.node(), Node::Op(LT, ..)) || matches!(*t.node(), Node::Op(_, a, b) if any_lt(&a) || any_lt(&b))
        }
        matches!(*t.node(), Node::Op(_, a, b) if any_lt(&a) || any_lt(&b))
    };
    for kind in ["subst", "wrap", "edit"] {
        let laws = mutate_laws(&seeds, 3, kind, 60, 5);
        assert!(!laws.is_empty(), "{kind}");
        for l in &laws {
            let (a, b) = l.split_once(" = ").map(|(a, b)| (parse_term(a), parse_term(b))).unwrap();
            assert!(!lt_inside(&a) && !lt_inside(&b), "{kind}: {l}");
            if kind != "edit" {
                assert!(a.is_law(&b, 3), "{kind}: {l}");
            }
        }
    }
}

/// `YIELD_FAMILY` (default add3), the proposer `PROPOSER=ngram|pool|stream|mutate` (or `YIELD_FILE`, one `lhs = rhs` per line) and `YIELD_N`
/// samples (default 2000); the family window the proposer is shown is the usual `RULEMINER_*` one (`STRIDE`, `PHASE`, `LAWS`). `stream`
/// replays the family's own sequence from `YIELD_SKIP` (default 1000) instead: the hash-ordered stream as a proposer, whose hard count is
/// M. With `CHECK_RULES` the rules in force decide cheap against hard. `YIELD_OUT` saves the proposed lines, `BAND_OUT` the hard ones
/// (`Cost::hard`, known or novel), as a stream for the loop. Prints a `YIELD` and a `BAND` line.
#[test]
#[ignore]
pub fn proposal_yield() {
    tatic::kernel::scoped(|| {
        std::panic::set_hook(Box::new(|_| {}));
        let family = env_var("YIELD_FAMILY").unwrap_or("add3");
        let kv = family_vars(&family);
        let n = env_or("YIELD_N", 2000usize);
        if let Some(path) = env_var("CHECK_RULES") {
            set_extra_rules(parse_rules(&std::fs::read_to_string(path).unwrap()));
        }
        SCORE_ONLY.with(|s| s.set(true));
        let strings = |laws: Vec<(String, Term, Term)>| -> Vec<String> { laws.into_iter().filter(|(_, a, b)| a.is_law(b, kv)).map(|(s, _, _)| s).collect() };
        let train_lines = strings(family_laws(&family, &env_or::<usize>, 4, kv, 7));
        let whole = |k: &str, d: usize| match k {
            "RULEMINER_STRIDE" => 1,
            "RULEMINER_PHASE" | "RULEMINER_SKIP" => 0,
            "RULEMINER_LAWS" => 1_000_000,
            _ => env_or::<usize>(k, d),
        };
        let known_lines = strings(family_laws(&family, &whole, 4, kv, 7));
        let lines: Vec<String> = match (env_var("YIELD_FILE"), env_var("PROPOSER")) {
            (Some(path), _) => std::fs::read_to_string(path).unwrap().lines().map(String::from).collect(),
            (_, Some("ngram")) => ngram_lines(&train_lines.join("\n"), env_or("YIELD_ORDER", 8usize), n, 1),
            (_, Some("pool")) => {
                let pool = pool3(&family, &env_or::<usize>).expect("pool proposer needs a three-variable family");
                let mut s = 7u64;
                (0..n).map(|_| format!("{} = {}", pool[lcg(&mut s) as usize % pool.len()].show(), pool[lcg(&mut s) as usize % pool.len()].show())).collect()
            }
            (_, Some("stream")) => {
                let held_out = |k: &str, d: usize| match k {
                    "RULEMINER_SKIP" => env_or("YIELD_SKIP", 1000usize),
                    "RULEMINER_LAWS" => n,
                    _ => env_or::<usize>(k, d),
                };
                strings(family_laws(&family, &held_out, 4, kv, 7))
            }
            (_, Some("mutate")) => {
                let seeds = read_laws(&env_var("MUTATE_SEEDS").expect("the mutate proposer needs MUTATE_SEEDS (a BAND_OUT file)"));
                mutate_laws(&seeds, kv, &env_var("MUTATE_KIND").unwrap_or("mix"), n, 11)
            }
            _ => panic!("set YIELD_FILE or PROPOSER=ngram|pool|stream|mutate"),
        };
        if let Some(out) = env_var("YIELD_OUT") {
            std::fs::write(out, lines.iter().map(|l| format!("{l}\n")).collect::<String>()).unwrap();
        }
        let laws = |lines: Vec<String>| lines.iter().filter_map(|l| parse_law(l, kv)).collect::<HashSet<_>>();
        let (train, known) = (laws(train_lines), laws(known_lines));
        let verdicts = classify_proposals(&lines, kv, &train, &known);
        let mut count: std::collections::BTreeMap<Verdict, usize> = Default::default();
        for (v, _) in &verdicts {
            *count.entry(*v).or_default() += 1;
        }
        println!("YIELD family={family} samples={} train={} known={} {count:?}", lines.len(), train.len(), known.len());
        let band: Vec<(&String, Cost)> = lines.iter().zip(&verdicts).filter_map(|(l, (_, c))| c.filter(Cost::hard).map(|c| (l, c))).collect();
        let mut steps: Vec<i64> = band.iter().map(|(_, c)| c.steps).collect();
        steps.sort();
        println!(
            "BAND {} hard of {} scored: {} not proved, {} machine proofs, median rule steps {}",
            band.len(),
            verdicts.iter().filter(|(_, c)| c.is_some()).count(),
            band.iter().filter(|(_, c)| !c.proved).count(),
            band.iter().map(|(_, c)| c.fallbacks).sum::<u64>(),
            steps.get(steps.len() / 2).copied().unwrap_or(0)
        );
        if let Some(out) = env_var("BAND_OUT") {
            std::fs::write(out, band.iter().map(|(l, _)| format!("{l}\n")).collect::<String>()).unwrap();
        }
    })
}

/// The verdicts separate the cases they name.
#[test]
pub fn classify_proposals_separates_cases() {
    let line = |s: &str| s.to_string();
    let lines = vec![
        line("add(x, y) = add(y, x)"),                 // a law, not in either set
        line("add(x, y) = sub(x, y)"),                 // refuted by the screen
        line("add(x, y"),                              // does not parse
        line("add(x, y) = add(x, y)"),                 // trivial
        line("add(y, x) = add(x, y)"),                 // the first one again, reversed
        line("add(x, z) = add(z, x)"),                 // in the training set
        line("add(x, add(y, z)) = add(add(x, y), z)"), // known to the family
        line("add(x, w) = add(w, x)"),                 // a variable outside the family
    ];
    let train: HashSet<(Term, Term)> = parse_law("add(x, z) = add(z, x)", 3).into_iter().collect();
    let known: HashSet<(Term, Term)> = parse_law("add(x, add(y, z)) = add(add(x, y), z)", 3).into_iter().collect();
    let scored = classify_proposals(&lines, 3, &train, &known);
    // a cost exactly for the laws that reach the kernel, and it agrees with the verdict
    for (v, c) in &scored {
        let graded = matches!(v, Verdict::KnownCheap | Verdict::KnownHard | Verdict::NovelCheap | Verdict::NovelHard);
        assert_eq!(c.is_some(), graded, "{v:?}");
        assert!(c.is_none_or(|c| c.hard() == matches!(v, Verdict::KnownHard | Verdict::NovelHard)), "{v:?} {c:?}");
    }
    let v: Vec<Verdict> = scored.iter().map(|(v, _)| *v).collect();
    assert!(matches!(v[0], Verdict::NovelCheap | Verdict::NovelHard), "{:?}", v[0]);
    assert_eq!(v[1..6], [Verdict::Refuted, Verdict::Unparsed, Verdict::Trivial, Verdict::Duplicate, Verdict::Memorised]);
    assert!(matches!(v[6], Verdict::KnownCheap | Verdict::KnownHard), "{:?}", v[6]);
    assert_eq!(v[7], Verdict::Unparsed);
}

/// The n-gram proposer reproduces its text's line shapes and is deterministic.
#[test]
pub fn ngram_lines_are_deterministic_and_line_shaped() {
    let text = "add(x, y) = add(y, x)\nsub(x, y) = sub(x, y)\nadd(x, add(y, z)) = add(add(x, y), z)";
    let (a, b) = (ngram_lines(text, 6, 20, 3), ngram_lines(text, 6, 20, 3));
    assert_eq!(a, b);
    assert!(a.iter().all(|l| l.len() <= 160 && !l.contains('\n')));
    assert!(a.iter().any(|l| l.contains(" = ")));
}
