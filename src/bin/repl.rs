//! An interactive read-parse-eval-print loop for tatic: parses each line
//! via `syntax::parse`, evaluates it through the JIT (`jit::JitEngine`,
//! falling back to the interpreter automatically the same way it always
//! does), and reports the result plus whether it got a kernel-checked
//! equivalence proof.
//!
//! `let NAME = EXPR` (with no `in`) defines `NAME` for use in later lines.
//! `syntax.rs`'s own parser has no notion of a scope that persists across
//! separate `parse` calls, so this works by literally re-parsing every
//! later line with `let NAME = EXPR in ` prefixed once per definition
//! seen so far -- terms are small and content-addressed here, so
//! re-parsing a previously-seen prefix costs a little repeated parsing,
//! not repeated storage, and this needed no changes to `syntax.rs`'s
//! public API.
//!
//! Type `:help` for commands, `:quit` (or Ctrl-D) to exit.

use std::io::{self, BufRead, Write};

use tatic::eval::EvalError;
use tatic::jit::{JitEngine, ProofStrength};
use tatic::syntax;
use tatic::term::TermStore;

fn print_help() {
    println!("tatic REPL");
    println!("  <expr>            parse, JIT-compile (or interpret), and evaluate an expression");
    println!("  let NAME = EXPR   define NAME for use in later lines (not recursive -- use `rec` for that)");
    println!("  :env              list current definitions");
    println!("  :help             this message");
    println!("  :quit             exit (or Ctrl-D)");
    println!();
    println!("Grammar: \\x y. body | let x = e1 in e2 | rec f x = body | if c then t else e");
    println!("         + - * / % < <= ==, standard precedence, application by juxtaposition");
}

/// A crude, word-boundary-safe heuristic for "is this a top-level `let`
/// definition (no `in`)" -- splits on whitespace and looks for a bare
/// `in` *token*, not a substring search, so it doesn't misfire on a name
/// like `int`. Good enough for a REPL prompt; not a real parse (`let`
/// with a malformed name or an empty RHS just falls through to being
/// evaluated as an ordinary expression, which then fails its own parse
/// with a normal error).
fn parse_top_level_let(line: &str) -> Option<(String, String)> {
    let rest = line.strip_prefix("let ")?.trim_start();
    if rest.split_whitespace().any(|w| w == "in") {
        return None; // has its own `in` -- an ordinary let-expression, not a definition
    }
    let (name, expr_src) = rest.split_once('=')?;
    let name = name.trim();
    let expr_src = expr_src.trim();
    let valid_name = !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    if !valid_name || expr_src.is_empty() {
        return None;
    }
    Some((name.to_string(), expr_src.to_string()))
}

/// `tail`, prefixed with `let name = expr in ` for every binding seen so
/// far, in order -- see the module docs for why this (rather than a
/// persistent parser scope) is how definitions carry across REPL turns.
fn with_bindings(bindings: &[(String, String)], tail: &str) -> String {
    let mut src = String::new();
    for (name, expr) in bindings {
        src.push_str("let ");
        src.push_str(name);
        src.push_str(" = ");
        src.push_str(expr);
        src.push_str(" in ");
    }
    src.push_str(tail);
    src
}

fn main() {
    print_help();
    println!();

    let mut store = TermStore::new();
    let mut jit = JitEngine::new();
    let mut bindings: Vec<(String, String)> = Vec::new();

    let stdin = io::stdin();
    loop {
        print!("tatic> ");
        if io::stdout().flush().is_err() {
            break;
        }
        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => {
                println!();
                break; // EOF (Ctrl-D)
            }
            Err(e) => {
                println!("input error: {e}");
                break;
            }
            Ok(_) => {}
        }
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        match line {
            ":quit" | ":q" => break,
            ":help" | ":h" => {
                print_help();
                continue;
            }
            ":env" => {
                if bindings.is_empty() {
                    println!("(no definitions yet)");
                } else {
                    for (name, expr) in &bindings {
                        println!("{name} = {expr}");
                    }
                }
                continue;
            }
            _ => {}
        }

        if let Some((name, expr_src)) = parse_top_level_let(line) {
            // Validate the definition parses (against everything defined
            // so far) before remembering it -- a bad definition should
            // report a parse error, not silently poison every later line.
            let probe = with_bindings(&bindings, &expr_src);
            match syntax::parse(&mut store, &probe) {
                Ok(_) => {
                    bindings.push((name.clone(), expr_src));
                    println!("defined `{name}`");
                }
                Err(e) => println!("parse error: {e}"),
            }
            continue;
        }

        let full_src = with_bindings(&bindings, line);
        let h = match syntax::parse(&mut store, &full_src) {
            Ok(h) => h,
            Err(e) => {
                println!("parse error: {e}");
                continue;
            }
        };

        match jit.apply(&store, h, &[]) {
            Ok(n) => println!(
                "= {n}  (kernel-checked equivalence proof: {})",
                match jit.proof_strength(h) {
                    ProofStrength::Universal => "yes -- covers every input",
                    // Deliberately not reported as a plain "yes": the
                    // certificates exist only at `jit.rs`'s sampled
                    // inputs, which say nothing about this call's own
                    // arguments.
                    ProofStrength::Samples => "only at the sampled inputs",
                    ProofStrength::None => "no",
                }
            ),
            Err(EvalError::TypeError) => {
                // Most likely an unapplied function value (this line
                // reduces to a Closure/Rec, not a plain Int) -- show its
                // printed form so the arity/shape is visible, and remind
                // how to apply it. Could also be a genuine internal type
                // mismatch, but the parser's own scoping already rules out
                // the usual causes of that.
                println!(
                    "(doesn't evaluate to a plain integer -- if this defines a function, apply it to arguments, e.g. `{} 1 2`)",
                    syntax::print(&store, h)
                );
            }
            Err(e) => println!("runtime error: {e:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn top_level_let_is_recognized() {
        assert_eq!(parse_top_level_let("let x = 5"), Some(("x".to_string(), "5".to_string())));
        assert_eq!(
            parse_top_level_let("let inc = \\y. y + 1"),
            Some(("inc".to_string(), "\\y. y + 1".to_string()))
        );
    }

    #[test]
    fn let_with_an_explicit_in_is_not_a_top_level_definition() {
        assert_eq!(parse_top_level_let("let x = 5 in x + 1"), None);
    }

    #[test]
    fn word_boundary_check_does_not_misfire_on_a_name_containing_in() {
        // "int" contains the substring "in" but is not the token `in`.
        assert_eq!(parse_top_level_let("let int = 5"), Some(("int".to_string(), "5".to_string())));
    }

    #[test]
    fn ordinary_lines_are_not_treated_as_definitions() {
        assert_eq!(parse_top_level_let("1 + 2"), None);
        assert_eq!(parse_top_level_let("let x = 5 in x"), None);
    }

    #[test]
    fn context_prefixes_every_binding_in_order() {
        let bindings = vec![("x".to_string(), "5".to_string()), ("y".to_string(), "x + 1".to_string())];
        assert_eq!(with_bindings(&bindings, "y * 2"), "let x = 5 in let y = x + 1 in y * 2");
    }
}
