//! Golden WAT snapshots, one per `samples::corpus()` term, plus a few `rejects_*`
//! terms the fragment must reject. A change to the lowering
//! (`src/lower_wat.rs`) or the builder that changes emitted WAT fails here.
//! If the change is intended, regenerate with
//! `UPDATE_GOLDEN=1 cargo test --test golden_wat` and review the diff. A
//! term the fragment rejects is recorded as `REJECTED`, so a new
//! acceptance or rejection shows up here too. The snapshots were first
//! recorded while the transitional `try_compile` asserted the IR path
//! byte-identical to the legacy direct emitter (since retired).

use std::fs;
use std::path::Path;

use tatic::compile::try_compile;
use tatic::samples;
use tatic::term::{Hash, TermStore};

/// Terms the fragment must reject, each in its own store. Nothing else
/// pins "identical rejections" now that the legacy emitter is gone.
fn rejects() -> Vec<(&'static str, TermStore, Hash)> {
    [
        // Comparisons only appear as an `If` condition.
        ("rejects_a_comparison_used_as_a_value", r"\x. x < 1"),
        ("rejects_a_non_comparison_condition", r"\x. if x + 1 then 1 else 2"),
        // An application headed by neither a variable nor a lambda.
        ("rejects_a_literal_applied_as_a_function", r"\x. 1 x"),
        // The self-reference is only ever called.
        ("rejects_a_self_reference_read_as_a_value", "rec f x = f"),
        // A lifted lambda cannot capture the enclosing `Rec`'s self-reference.
        ("rejects_a_nested_closure_capturing_self", r"rec f n = (\y. f y) n"),
    ]
    .into_iter()
    .map(|(name, src)| {
        let mut s = TermStore::new();
        let h = tatic::syntax::parse(&mut s, src).unwrap();
        (name, s, h)
    })
    .collect()
}

/// Compares `got` against `dir/name.wat` (CRLF-normalised), or writes it
/// there when `update`. Otherwise, on a mismatch, pushes `name` onto
/// `changed` rather than failing immediately, so a whole corpus can be
/// checked and reported in one assertion.
fn check_golden(dir: &Path, name: &str, got: &str, update: bool, changed: &mut Vec<String>) {
    let path = dir.join(format!("{name}.wat"));
    if update {
        fs::create_dir_all(dir).unwrap();
        fs::write(&path, got).unwrap();
        return;
    }
    let want = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}; run with UPDATE_GOLDEN=1 to record it", path.display()));
    if want.replace("\r\n", "\n") != got {
        changed.push(name.to_string());
    }
}

#[test]
fn every_benchmark_term_lowers_to_its_golden_wat() {
    let update = std::env::var_os("UPDATE_GOLDEN").is_some();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("golden");
    let mut changed = Vec::new();
    for (name, s, h) in samples::corpus().into_iter().chain(rejects()) {
        let got = match try_compile(&s, h) {
            Some(frag) => frag.wat,
            None => "REJECTED\n".to_string(),
        };
        // So that `UPDATE_GOLDEN=1` cannot quietly record one as accepted.
        assert!(!name.starts_with("rejects_") || got == "REJECTED\n", "{name} should be rejected, but compiled to:\n{got}");
        check_golden(&dir, name, &got, update, &mut changed);
    }
    assert!(changed.is_empty(), "emitted WAT changed for {changed:?}; if intended, rerun with UPDATE_GOLDEN=1 and review the diff");
}

#[test]
fn specialised_benchmark_terms_lower_to_their_golden_wat() {
    let update = std::env::var_os("UPDATE_GOLDEN").is_some();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("golden");
    let mut changed = Vec::new();
    let terms: [(&str, fn(&mut TermStore) -> Hash); 2] =
        [("partial_application_loop", samples::partial_application_loop), ("capturing_closure_loop", samples::capturing_closure_loop)];
    for (name, build) in terms {
        let mut s = TermStore::new();
        let h = build(&mut s);
        let c = tatic::compile::compile_specialised(&s, h).unwrap_or_else(|| panic!("{name} should compile"));
        assert!(c.specialised.is_some(), "{name} should be specialised");
        check_golden(&dir, &format!("{name}_specialised"), &c.frag.wat, update, &mut changed);
    }
    assert!(changed.is_empty(), "emitted WAT changed for {changed:?}; if intended, rerun with UPDATE_GOLDEN=1 and review the diff");
}
