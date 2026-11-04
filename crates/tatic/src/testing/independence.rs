//! Test-only: the decompiler and the specialisation checker are trusted
//! only because they share no code with what they check. This enforces
//! that mechanically, over the code above a file's `#[cfg(test)] mod tests`
//! (the tests may use anything).

/// Panics if `src` (the contents of `file`), above its test module and
/// ignoring `//` comments:
/// - contains any token in `forbidden`. The check is token by token, so
///   `use crate :: compile :: peel;` or `use crate::{compile::peel};`
///   can't slip past a substring match.
/// - uses `super::super`.
/// - aliases a path root (`use crate as x`, `extern crate self as x`, and
///   the same for `super` and `tatic`): `x::eval` would then need no
///   `crate::`. Any `crate`, `self`, `super` or `tatic` token followed by
///   `as` counts, even across a line break.
/// - has a `crate::`, `super::` or `tatic::` path that does not start with
///   one of `allowed` (module paths such as `lang::term`, matched on whole
///   segments). All three are scanned because `super::` and, in test
///   builds, `tatic::` (`lib.rs` has `extern crate self as tatic`) can
///   reach the same modules as `crate::`. `crate::{..}` has an empty path
///   and is rejected too.
pub(crate) fn assert_independent(file: &str, src: &str, forbidden: &[&str], allowed: &[&str]) {
    let lines: Vec<&str> = src.lines().collect();
    let tests_start = lines
        .iter()
        .enumerate()
        .find(|(i, l)| l.trim() == "#[cfg(test)]" && lines.get(i + 1).is_some_and(|next| next.trim_start().starts_with("mod tests")))
        .map_or(lines.len(), |(i, _)| i);
    let code: Vec<&str> = lines[..tests_start].iter().map(|l| l.trim_start()).filter(|l| !l.starts_with("//")).collect();
    for tok in forbidden {
        let hit = code.iter().any(|l| l.split(|c: char| !c.is_alphanumeric() && c != '_').any(|t| t == *tok));
        assert!(!hit, "{file} must not use {tok}");
    }
    assert!(!code.iter().any(|l| l.contains("use super::super")), "{file} must not use super::super");
    let tokens: Vec<&str> = code.iter().flat_map(|l| l.split(|c: char| !c.is_alphanumeric() && c != '_')).filter(|t| !t.is_empty()).collect();
    for w in tokens.windows(2) {
        assert!(!(["crate", "self", "super", "tatic"].contains(&w[0]) && w[1] == "as"), "{file} must not alias {} (`{} as`)", w[0], w[0]);
    }
    for l in &code {
        // Collapse whitespace so `crate :: compile` can't dodge the
        // `crate::` search. `pub(crate)` has no `::` after `crate`, so it
        // never matches.
        let compact: String = l.chars().filter(|c| !c.is_whitespace()).collect();
        for prefix in ["crate::", "super::", "tatic::"] {
            let mut rest = compact.as_str();
            while let Some(i) = rest.find(prefix) {
                let after = &rest[i + prefix.len()..];
                let ident = |c: char| c.is_alphanumeric() || c == '_';
                let Some(ok) = allowed.iter().find(|a| after.strip_prefix(**a).is_some_and(|r| !r.starts_with(ident))) else {
                    let end = after.find(|c: char| !ident(c) && c != ':').unwrap_or(after.len());
                    panic!("{file} must not use {prefix}{} (only {allowed:?} are allowed)", &after[..end]);
                };
                rest = &after[ok.len()..];
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::assert_independent;

    fn rejected(src: &str) -> bool {
        std::panic::catch_unwind(|| assert_independent("x.rs", src, &["compile"], &["lang::term"])).is_err()
    }

    #[test]
    fn allowed_paths_pass_and_others_fail() {
        assert!(!rejected("use crate::lang::term::Hash;\n"));
        assert!(!rejected("use crate::lang::term;\n"));
        assert!(rejected("use crate::lang::termx::Hash;\n"));
        assert!(rejected("use crate::lang::syntax;\n"));
        assert!(rejected("use crate::lang::eval;\n"));
        assert!(rejected("use super::eval;\n"));
        assert!(rejected("use tatic::lang::eval;\n"));
        assert!(rejected("use crate :: compile :: peel;\n"));
    }

    #[test]
    fn an_alias_of_the_crate_root_fails() {
        // Each would let `x::eval` through, since no `crate::` follows.
        for src in ["use crate as x;\n", "use crate as\n    x;\n", "extern crate self as x;\n", "use tatic as x;\n", "use super as x;\n"] {
            assert!(rejected(src), "{src:?}");
        }
    }
}
