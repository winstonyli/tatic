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
/// - has a `crate::` or `super::` path whose first segment is not in
///   `allowed`. Both prefixes are scanned because a module directly under
///   the crate root reaches the same siblings through `super::` as through
///   `crate::`. `crate::{..}` has an empty first segment and is rejected
///   too.
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
    for l in &code {
        // Collapse whitespace so `crate :: compile` can't dodge the
        // `crate::` search. `pub(crate)` has no `::` after `crate`, so it
        // never matches.
        let compact: String = l.chars().filter(|c| !c.is_whitespace()).collect();
        for prefix in ["crate::", "super::"] {
            let mut rest = compact.as_str();
            while let Some(i) = rest.find(prefix) {
                let after = &rest[i + prefix.len()..];
                let end = after.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(after.len());
                let head = &after[..end];
                assert!(allowed.contains(&head), "{file} must not use {prefix}{head} (only {allowed:?} are allowed)");
                rest = &after[end..];
            }
        }
    }
}
