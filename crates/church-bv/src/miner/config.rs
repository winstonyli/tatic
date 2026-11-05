use super::*;

/// The phase clock: `phase(label)` prints the seconds since the previous mark.
pub(super) struct Clock(pub(super) std::cell::Cell<Instant>);

impl Clock {
    pub(super) fn phase(&self, label: &str) {
        println!("RULEMINER time {label}: {:.1}s", self.0.replace(Instant::now()).elapsed().as_secs_f64());
    }
}

/// Every `RULEMINER_*` switch of `rule_miner`, read once (defaults in `new`), except the law window's (`RULEMINER_LAWS`,
/// `_PHASE`, `_SKIP`), which the driver reads when it writes the law file (`driver::write_laws`).
pub struct MinerConfig {
    /// `RULEMINER_ROUNDS`: greedy rounds (default no cap: the mine stops when no candidate gains; a cap trimmed general rules,
    /// docs/tier-cycle/ "cmp3d's library lost its general rules").
    pub rounds: usize,
    /// `RULEMINER_THREADS`: scoring threads, clamped to 1..=12.
    pub threads: usize,
    /// `RULEMINER_FAST` (switch, off by default): score without rule proofs, proving only each round's winner.
    pub fast: bool,
    /// `RULEMINER_BASE=<file>`: rules (`lhs -> rhs` lines) in force throughout (section 74).
    pub base: Option<String>,
    /// `RULEMINER_LAWFILE=<file>` (required): mine from these `lhs = rhs` lines.
    pub lawfile: String,
    /// `RULEMINER_GUARD=<k>`: about k machine-free laws scored with the stragglers (default 120, 0 = off).
    pub guard: usize,
    /// `RULEMINER_NODUPLHS` (switch, on by default): drop candidates whose left side already has a rule in `base`.
    pub no_dup_lhs: bool,
    /// `RULEMINER_EXTRAS_FROM=<i>`, `_KEEP=<n>`, `_BY=first|small|ctx` (all three or none): the lawfile's laws from line `i` are a
    /// pool of extras and the mine keeps `n` of them (`kept_indices`); the laws before `i` are always read.
    pub extras: Option<ExtrasKeep>,
    /// `RULEMINER_POOL_DUMP=<prefix>` (with `extras` by `first`): before cutting the pool, classify it and write the raw facts
    /// the context scorer needs to `<prefix>_pool.tsv` (`ctx_scorer::pool_tsv`) and `<prefix>_served.txt` (the served
    /// stragglers' normal forms); the mine itself runs as without it.
    pub pool_dump: Option<String>,
    /// `RULEMINER_CTX_WEIGHTS=<file>` (required by `_BY=ctx`): the context model's weights (`ctx_scorer::LAYOUT`).
    pub ctx_weights: Option<String>,
}

/// How a mine picks its extras from the pool: `First` the first `n`, `Small` the stragglers the base rules leave, fewest
/// rewrite steps then smallest normal form first, any shortfall filled with the pool's other laws in order
/// (docs/superpowers/specs/2026-10-31-context-aware-selector-design.md); `Ctx` the same stragglers, highest context-model score
/// first (`RULEMINER_CTX_WEIGHTS`, docs/superpowers/specs/2026-11-01-context-aware-scorer-design.md).
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Keep {
    First,
    Small,
    Ctx,
}

impl Keep {
    /// The driver variable `EXTRAS_SELECT` / `RULEMINER_EXTRAS_BY`.
    pub fn parse(s: &str) -> Result<Keep, String> {
        match s {
            "first" => Ok(Keep::First),
            "small" => Ok(Keep::Small),
            "ctx" => Ok(Keep::Ctx),
            _ => Err(format!("EXTRAS_SELECT: expected first, small or ctx, got {s}")),
        }
    }
}

/// The lawfile's pool of extras starts at line `from`; the mine keeps `n` of it, chosen `by`.
#[derive(Clone, Copy, Debug)]
pub struct ExtrasKeep {
    pub from: usize,
    pub n: usize,
    pub by: Keep,
}

impl MinerConfig {
    pub fn new(s: &Setup) -> Self {
        MinerConfig {
            rounds: s.or("RULEMINER_ROUNDS", usize::MAX),
            threads: s.or("RULEMINER_THREADS", 1).clamp(1, 12),
            fast: s.flag("RULEMINER_FAST", false),
            base: s.var("RULEMINER_BASE").map(String::from),
            lawfile: s.var("RULEMINER_LAWFILE").expect("RULEMINER_LAWFILE: the laws to mine").to_string(),
            guard: s.or("RULEMINER_GUARD", 120),
            no_dup_lhs: s.flag("RULEMINER_NODUPLHS", true),
            extras: s.var("RULEMINER_EXTRAS_FROM").map(|from| {
                let need = |k: &str| s.var(k).unwrap_or_else(|| panic!("RULEMINER_EXTRAS_FROM needs {k}"));
                let num = |k: &str| need(k).parse::<usize>().unwrap_or_else(|_| panic!("{k}={} is not a count", need(k)));
                ExtrasKeep {
                    from: from.parse().unwrap_or_else(|_| panic!("RULEMINER_EXTRAS_FROM={from} is not a count")),
                    n: num("RULEMINER_EXTRAS_KEEP"),
                    by: Keep::parse(need("RULEMINER_EXTRAS_BY")).unwrap_or_else(|e| panic!("RULEMINER_EXTRAS_BY: {e}")),
                }
            }),
            pool_dump: s.var("RULEMINER_POOL_DUMP").map(String::from),
            ctx_weights: s.var("RULEMINER_CTX_WEIGHTS").map(String::from),
        }
    }
}

