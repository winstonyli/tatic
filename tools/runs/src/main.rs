//! `runs`: gates, timings and machine state for church_bv's sweeps, in one tool (README, "Benchmarks").
#[cfg(not(windows))]
compile_error!("tools/runs is Windows-only: it measures runs with job objects and reads Windows' machine state");

mod state;
#[cfg(test)]
mod state_tests;

const USAGE: &str = "usage:
  runs state";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let code = match dispatch(&args) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("runs: {e}\n{USAGE}");
            2
        }
    };
    std::process::exit(code);
}

fn dispatch(args: &[String]) -> Result<i32, String> {
    let (cmd, _rest) = args.split_first().ok_or("no command")?;
    match cmd.as_str() {
        "state" => {
            println!("{}", state::line());
            Ok(0)
        }
        _ => Err(format!("unknown command {cmd}")),
    }
}
