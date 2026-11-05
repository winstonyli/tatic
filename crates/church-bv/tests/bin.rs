//! The built `church-bv` binary: its exit statuses and subcommand list (the entries themselves are the old ignored tests).

use std::process::{Command, Stdio};

fn run(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_church-bv")).args(args).stdin(Stdio::null()).output().expect("start church-bv")
}

#[test]
fn no_subcommand_exits_2_and_lists_names() {
    let out = run(&[]);
    assert_eq!(out.status.code(), Some(2));
    let text = String::from_utf8_lossy(&out.stderr);
    for name in ["sweep", "worker", "loop-stream", "proof-cost-split", "rule-set-kernel-check", "ctx-fit", "overlap-report", "q1-report"] {
        assert!(text.contains(name), "usage lacks {name}: {text}");
    }
}

#[test]
fn unknown_subcommand_exits_2() {
    assert_eq!(run(&["nonsense"]).status.code(), Some(2));
}

#[test]
fn worker_with_closed_stdin_exits_0() {
    assert_eq!(run(&["worker"]).status.code(), Some(0));
}
