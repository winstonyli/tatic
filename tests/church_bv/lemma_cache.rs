//! The lemma statements a loop's processes share, or a whole sweep's (`LEMMA_CACHE=<file>`, set by `driver::run_loop`): a
//! process binds a statement an earlier process checked without building or checking its proof again. Sound because a lemma is
//! only ever used as a parameter of its statement (`rewrite::shared_lemma`) and every statement in the file was checked by
//! a process of this same build (the header holds a hash of the exe); a wrong key can only make a later check fail.
//! `LEMMA_RECHECK=1` builds and checks every lemma anyway and asserts the file's statement equals the built one.

use super::*;
use hashbrown::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::{Mutex, OnceLock};

const MAGIC: &[u8; 4] = b"TLC1";

/// A cache file's entries: key -> the statement in `tatic::kernel::bin` form.
pub struct Cache {
    entries: HashMap<String, Vec<u8>>,
    /// keys in file order, so a save keeps it
    order: Vec<String>,
    /// why the file was not used, when it was not
    pub why_empty: Option<String>,
}

fn parse(b: &[u8], identity: u64) -> Result<(HashMap<String, Vec<u8>>, Vec<String>), String> {
    if b.len() < 12 || &b[..4] != MAGIC {
        return Err("not a lemma cache".into());
    }
    if u64::from_le_bytes(b[4..12].try_into().unwrap()) != identity {
        return Err("written by another build".into());
    }
    let (mut pos, mut entries, mut order) = (12, HashMap::new(), vec![]);
    let field = |pos: &mut usize| -> Result<&[u8], String> {
        let len = b.get(*pos..*pos + 4).ok_or("truncated")?;
        let len = u32::from_le_bytes(len.try_into().unwrap()) as usize;
        let v = b.get(*pos + 4..*pos + 4 + len).ok_or("truncated")?;
        *pos += 4 + len;
        Ok(v)
    };
    while pos < b.len() {
        let key = String::from_utf8(field(&mut pos)?.to_vec()).map_err(|_| "a key is not UTF-8")?;
        let stmt = field(&mut pos)?.to_vec();
        if entries.insert(key.clone(), stmt).is_none() {
            order.push(key);
        }
    }
    Ok((entries, order))
}

impl Cache {
    /// The file at `path` if `identity` wrote it, else an empty cache saying why.
    pub fn load(path: &Path, identity: u64) -> Cache {
        let parsed = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display())).and_then(|b| parse(&b, identity));
        match parsed {
            Ok((entries, order)) => Cache { entries, order, why_empty: None },
            Err(why) => Cache { entries: HashMap::new(), order: vec![], why_empty: Some(why) },
        }
    }
    pub fn get(&self, key: &str) -> Option<&[u8]> {
        self.entries.get(key).map(|v| v.as_slice())
    }
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    /// Writes this cache's entries, then those of `new` whose key is not there yet (the first of a key wins), to a temporary
    /// file renamed over `path`. Returns (entries, bytes) written.
    pub fn save(&self, path: &Path, identity: u64, new: &[(String, Vec<u8>)]) -> std::io::Result<(usize, usize)> {
        let mut out = MAGIC.to_vec();
        out.extend(identity.to_le_bytes());
        let mut seen: HashSet<&str> = HashSet::new();
        for (k, s) in self.order.iter().map(|k| (k, &self.entries[k])).chain(new.iter().map(|(k, s)| (k, s))) {
            if seen.insert(k) {
                for f in [k.as_bytes(), s] {
                    out.extend((f.len() as u32).to_le_bytes());
                    out.extend(f);
                }
            }
        }
        let tmp = path.with_extension("bin.tmp");
        std::fs::write(&tmp, &out)?;
        std::fs::rename(&tmp, path)?;
        Ok((seen.len(), out.len()))
    }
}

/// A hash of this exe's bytes: the build that wrote a file. Hashed once per process (the exe does not change while it runs).
fn exe_identity() -> u64 {
    static ID: OnceLock<u64> = OnceLock::new();
    *ID.get_or_init(|| {
        use std::hash::{Hash, Hasher};
        let bytes = std::fs::read(std::env::current_exe().unwrap()).expect("read the running exe");
        let mut h = std::collections::hash_map::DefaultHasher::new();
        bytes.hash(&mut h);
        h.finish()
    })
}

struct Process {
    path: PathBuf,
    identity: u64,
    cache: Cache,
}

/// This task's cache (the file is read again in each `driver::worker` task, which sees the earlier tasks' saves) and
/// counters.
static PROCESS: crate::task::PerTaskArc<Option<Process>> = crate::task::PerTaskArc::new();
static RECORDED: crate::task::PerTask<Mutex<Vec<(String, Vec<u8>)>>> = crate::task::PerTask::new();
static HITS: crate::task::PerTask<AtomicU64> = crate::task::PerTask::new();
static BUILT: crate::task::PerTask<AtomicU64> = crate::task::PerTask::new();
static SKIPPED: crate::task::PerTask<AtomicU64> = crate::task::PerTask::new();

/// This task's cache, read at first use; holding `None` without `LEMMA_CACHE`.
fn process() -> std::sync::Arc<Option<Process>> {
    PROCESS.get(|| {
        let path = PathBuf::from(env_var("LEMMA_CACHE")?);
        let identity = exe_identity();
        let cache = Cache::load(&path, identity);
        if let Some(why) = &cache.why_empty {
            eprintln!("LEMMA_CACHE starts empty: {why}");
        }
        Some(Process { path, identity, cache })
    })
}

/// Whether `LEMMA_RECHECK=1`: build and check every lemma, comparing the cached statements with the built ones.
pub fn recheck() -> bool {
    static R: crate::task::PerTask<bool> = crate::task::PerTask::new();
    *R.get(|| env_var("LEMMA_RECHECK").is_some_and(|v| v == "1"))
}

/// The statement an earlier process checked for `key`, if the cache has one.
pub fn lookup(key: &str) -> Option<Expr> {
    let p = process();
    let b = (*p).as_ref()?.cache.get(key)?;
    match tatic::kernel::bin::read(b) {
        Ok(s) => {
            HITS.get(Default::default).fetch_add(1, Relaxed);
            Some(s)
        }
        Err(e) => {
            eprintln!("LEMMA_CACHE entry {key} unreadable ({e}), rebuilding it");
            None
        }
    }
}

/// Keeps `stmt`, which this process just checked, for the next process. A statement that is not closed is not kept.
pub fn record(key: &str, stmt: &Expr) {
    if process().is_none() {
        return;
    }
    BUILT.get(Default::default).fetch_add(1, Relaxed);
    match (stmt.loose() == 0 && stmt.free() == 0).then(|| tatic::kernel::bin::write(stmt)) {
        Some(Ok(b)) => RECORDED.get(Default::default).lock().unwrap_or_else(|e| e.into_inner()).push((key.to_string(), b)),
        _ => {
            SKIPPED.get(Default::default).fetch_add(1, Relaxed);
        }
    }
}

/// Saves the cache when dropped (at every return of a test that builds lemmas, and on unwind: the recorded statements were
/// all checked). Never panics.
pub struct Save;

impl Drop for Save {
    fn drop(&mut self) {
        // a task that never looked anything up has nothing to add
        let Some(arc) = PROCESS.peek() else { return };
        let Some(p) = &*arc else { return };
        let new = std::mem::take(&mut *RECORDED.get(Default::default).lock().unwrap_or_else(|e| e.into_inner()));
        let saved = if new.is_empty() { Ok((p.cache.len(), 0)) } else { p.cache.save(&p.path, p.identity, &new) };
        match saved {
            Ok((n, bytes)) => eprintln!(
                "LEMMA_CACHE loaded={} hits={} built={} saved={n} skipped={} bytes={bytes}",
                p.cache.len(),
                HITS.get(Default::default).load(Relaxed),
                BUILT.get(Default::default).load(Relaxed),
                SKIPPED.get(Default::default).load(Relaxed)
            ),
            Err(e) => eprintln!("LEMMA_CACHE save to {} failed: {e}", p.path.display()),
        }
    }
}

#[test]
fn lemma_cache_round_trips_and_rejects_other_builds() {
    let dir = std::env::temp_dir().join(format!("tatic_lemma_cache_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("lemmas.bin");
    let _ = std::fs::remove_file(&path);
    let stmt = |k: usize| lemma_n_ty(k, &|v| id(bool0(), xor(v[0], v[k - 1]), xor(v[k - 1], v[0])));
    let enc = |k: usize| tatic::kernel::bin::write(&stmt(k)).unwrap();
    let fresh = Cache::load(&path, 7);
    assert!(fresh.why_empty.is_some() && fresh.len() == 0);
    assert_eq!(fresh.save(&path, 7, &[("a".into(), enc(2)), ("b".into(), enc(3)), ("a".into(), enc(3))]).unwrap().0, 2, "first of a key wins");
    // a second process adds to what the first saved
    let second = Cache::load(&path, 7);
    assert!(second.why_empty.is_none() && second.len() == 2);
    second.save(&path, 7, &[("b".into(), enc(4)), ("c".into(), enc(4))]).unwrap();
    let third = Cache::load(&path, 7);
    let got = |k: &str| tatic::kernel::bin::read(third.get(k).unwrap()).unwrap();
    assert!(got("a") == stmt(2) && got("b") == stmt(3) && got("c") == stmt(4));
    // another build's file, a foreign file and a truncated one are not used
    assert!(Cache::load(&path, 8).why_empty.unwrap().contains("another build"));
    let bytes = std::fs::read(&path).unwrap();
    std::fs::write(&path, &bytes[..bytes.len() - 1]).unwrap();
    assert!(Cache::load(&path, 7).why_empty.unwrap().contains("truncated"));
    std::fs::write(&path, b"something else entirely").unwrap();
    assert!(Cache::load(&path, 7).why_empty.unwrap().contains("not a lemma cache"));
    std::fs::remove_dir_all(&dir).unwrap();
}
