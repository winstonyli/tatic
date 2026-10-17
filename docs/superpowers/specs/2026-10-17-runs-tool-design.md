---
status: done
---

# `runs`: one Rust tool for gates, timings and machine state

Date: 2026-10-17. Status: built (`tools/runs`, 98104e7 and the commits before it, through 6d40f0e). Survey behind it: docs/tier-cycle.md, "Survey: workflow time outside the sweep".

## Goal

Replace the gate, timing and machine-state scripts, written in four languages, with one Rust crate. It should:
- measure each run the same way;
- put no measurement processes inside the measured job;
- take machine state natively, in milliseconds rather than 5 s of PowerShell.

Outputs of the church_bv sweeps do not change; only how they are launched, compared and timed.

## What it replaces

| Today | Language | Becomes |
|---|---|---|
| `docs/runs/2026-10-12/scripts/hc_seq.sh` (four gate sweeps) | bash | `runs gate` |
| `.../gate_cmp.py`, `.../gate_cmp_check.sh` | Python, bash | `runs cmp` (and `runs gate`'s last step); the check becomes a unit test |
| `.../hc_rounds.ps1` (twelve alternating sweeps) | PowerShell | `runs time --sweep` |
| `.../sweep_job.ps1` (one sweep in a job object) | PowerShell + C# | `runs run` (one measured run) |
| `.../cpu_ab.ps1`, `.../cpu_arms.ps1` (env-var arms of `proof_cost_split`, rotating) | PowerShell | `runs time` with arms that differ in environment |
| `scripts/quiet_ab/` (`ab.sh`, `pin.sh`, `pin.ps1`, `sampler.ps1`, `clean.py`, `test_clean.sh`): quiet waits, a CPU sampler, discarding runs others loaded | bash, PowerShell, Python | `runs time`; the cleaning rule's test becomes a unit test |
| `.../kk.ps1` (run directory) | PowerShell | `runs dir` |
| `.../sweep_xperf.ps1` (xperf around one sweep) | PowerShell | stays a PowerShell (it drives xperf, elevated), but runs its sweep with `runs run` and finds the run directory with `runs dir` |
| `tests/church_bv/machine.rs`'s `machine_state()` (PowerShell, about 5 s wall and 1 s CPU) | Rust calling PowerShell | `tools/runs/src/state.rs` (native; church_bv includes the same file) |

`scripts/bench_ab.sh` (criterion benches across a worktree of another revision) is not part of this: it builds revisions and reads criterion's output. It is a different job, and nothing here overlaps it.

**Kept:** `docs/runs/2026-10-12/scripts/kk.sh`.
- About 50 historical run scripts call it, and they are the record of what ran.
- `runs dir` computes the same directory, and a unit test checks that the two agree.
- Ruling: keep it rather than rewrite the historical scripts. Cost if wrong: one sed over those scripts later.

## Layout

- **Crate:** `tools/runs/` (the directory `tools/` exists already, holding `shr_probe.py`), package `tatic-runs`, a binary `runs` only. Its modules are `job`, `state`, `cmp`, `time` and `main`.
  - It is not a workspace member, and the root package has no `[workspace]`.
  - It has its own `Cargo.lock` and target directory (`tools/runs/target`), so building it never takes the church_bv build's cargo lock.
  - Because it is separate, the gate and timing code does not change with the exes it compares.
- **Build:** `cargo build --release --manifest-path tools/runs/Cargo.toml`. Run it as `tools/runs/target/release/runs.exe`. README's Quick start gets that line.
- **Dependencies:** `windows-sys` 0.61, with the features for job objects, threading, Toolhelp and process creation. `job`, `time` and `main` use it.

  And `regex` 1 (1.13.1 is in the local registry already): `cmp` keeps `gate_cmp.py`'s regular expressions as they are, in byte mode (`(?-u)`), and `time --grep` takes one. Argument parsing is hand-written, as the subcommands are few. Ruling (plan): the earlier "nothing else" would have meant hand-written matchers for both; cost if wrong: one dependency in a crate with its own lock.
- **`state` is shared by source, not by dependency.**
  - `tools/runs/src/state.rs` declares its Win32 calls in its own `extern "system"` blocks, as `driver.rs`'s `stdio` does, and depends on nothing but std.
  - church_bv includes that same file: `#[cfg(windows)] #[path = "../../tools/runs/src/state.rs"] mod state;` in machine.rs.
  - So nothing is added to the root `Cargo.toml` or `Cargo.lock`. An edit to the rest of `tools/runs` never rebuilds church_bv or changes the exes `gate` compares; only an edit to `state.rs` does.
  - `state.rs`'s header says that church_bv compiles it, so it must stay dependency-free.
- **Platform:** off Windows, machine.rs keeps printing "machine state unavailable", as today. `tools/runs` is Windows-only (`compile_error!` elsewhere), and says so.
- **`.gitignore`:** add `/tools/runs/target`.

## Measured runs (`runs::job`)

One function, `run(spec) -> RunResult`, used by `run`, `time` and `gate`. A `RunSpec` holds:
- **The exe:** canonicalised against `runs`'s own working directory before the start. Rust would otherwise resolve a relative path against the parent's directory, not the child's (`pin.ps1` once had the same bug; RELATED_WORK §66).
- **Arguments.**
- **Environment:** additions (`VAR=val`) and removals (`VAR=` with an empty value removes it, as `cpu_ab.ps1`'s old arm unset its variable).
- **The working directory.**
- **Output:** either one output file that takes both streams through one handle, cloned (`gate`'s `log.txt`, as `> log.txt 2>&1`, so the interleaving is the one today's runs have), or separate stdout and stderr files.
- the priority (default BelowNormal; Normal for GPU-feeding jobs, LONG_RUNS.md) and the affinity mask (default `0xFFF`: 12 of 16 cores).

How it runs:
- **Into the job before it starts.** The exe is started with `CREATE_SUSPENDED` (std's `CommandExt::creation_flags`) and assigned to a new job object. Its one thread is then resumed: Toolhelp32 snapshot of the process's threads, `OpenThread`, `ResumeThread`.
  - So every process it starts is in the job, with no race. Today `pin.ps1` assigns after the start, and `sweep_job.ps1` assigns the launcher itself.
  - Rejected: calling `CreateProcessW` directly, which returns the thread handle but means redoing std's environment and handle setup.
  - If `AssignProcessToJobObject` fails (for example, a parent job's affinity limit rejects the mask), the run is not started: the process is terminated, and `runs` reports why. `pin.ps1` fell back to counting the launched process only. That made the number mean something else, so here a failure is an error.
- **The end of a run:** after the main process exits, `runs` polls the job's `ActiveProcesses` down to zero, on a 60 s deadline (`sweep_job.ps1`'s note: the job counts until its last process exits).
  - It reads the accounting and the end `GetSystemTimes` only after that.
  - Processes still alive at the deadline are reported as `stragglers=<n>`, and closing the job kills them.
- **Limits on the job, not per process:** `JOBOBJECT_EXTENDED_LIMIT_INFORMATION` sets `JOB_OBJECT_LIMIT_PRIORITY_CLASS`, `JOB_OBJECT_LIMIT_AFFINITY` and `JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE`.
  - These apply to every process in the job.
  - If `runs` dies, Windows kills the run's whole tree: no orphans.
- **`RunResult`:**
  - exit code, wall time;
  - job CPU (user plus kernel, from `JOBOBJECT_BASIC_ACCOUNTING_INFORMATION`; the split is not reported, LONG_RUNS.md);
  - total processes;
  - peak process and peak job commit (extended limit information);
  - the machine during the run (next section).
- **During the run,** a sampler thread wakes every 2 s:
  - It reads `GetSystemTimes`: busy = kernel + user − idle, summed over all processors.
  - It lists processes (Toolhelp32) whose names match the "others' jobs" patterns. These default to `selfplay*` and `League*`, as `quiet_ab` has; `--others` replaces the list. Matching ignores case and drops `.exe`, as PowerShell's `-like` on `ProcessName` did.
  - Bias: `GetSystemTimes`'s busy time includes interrupt and DPC time that no job is charged, so the other load reads slightly high. `clean.py` had the same bias, since it worked from `% Processor Time`.
  - `runs` and its sampler thread run at BelowNormal, as `ab.sh` set itself and its sampler.
  - It also takes one reading at the start and one at the end.
  - From these: the load of other processes is (machine busy time − the job's CPU) / (wall × logical processors), as a percentage. That is the subtraction `clean.py` does, here from the tool's own exact numbers. Plus the largest count of other jobs' processes seen.
  - It replaces `sampler.ps1`'s separate PowerShell, whose `Get-Counter` sampling cost CPU of its own.

## Machine state (`tools/runs/src/state.rs`)

- **`cpu`:**
  - `cpu_load(window)` is `GetSystemTimes` before and after the window: the machine's busy percentage.
  - `Load::since(snapshot)` gives the load since an earlier reading, with no wait.
- **`lockpriv`:** `OpenProcessToken` and `GetTokenInformation(TokenPrivileges)`; is `SeLockMemoryPrivilege` present (enabled or not)? Same meaning as today's `whoami /priv` match.
- **`rtp`:** Defender's real-time protection, as `Some(bool)` or `None` (unknown).
  - Load `%ProgramFiles%\Windows Defender\MpClient.dll` with `LoadLibraryW`. Call `MpManagerOpen(0, &h)`, `MpManagerStatusQueryEx(h, 0, buf)` on a zeroed 8 KB buffer, then `MpHandleClose`.
  - If `ProductStatus & MP_STATUS_FLAG_SERVICE_UNAVAILABLE` (bit 0): `Some(false)`. The service is not running, so nothing protects in real time. Measured 8 ms on this machine.
  - Otherwise, or if the DLL or a call fails: one `powershell -NoProfile -Command (Get-MpComputerStatus).RealTimeProtectionEnabled`. That is 0.8-1.0 s and 0.7 s CPU, outside any measured job; `None` if that fails too.
  - Not used: the `Component[MPCOMPONENT_REALTIME_MONITOR]` field. Its offset depends on undocumented nested sizes, and it was not testable with the service stopped. If the service is ever running, a probe can check it against `Get-MpComputerStatus` and replace the fallback.
- **`line()`:** the one-line form, `RTP=False CPU=18% lockpriv=True`.
  - `CPU` is the load over a 2 s window: the same window as today, but a wait in this thread, not a PowerShell.
  - machine.rs appends `pages=` as now: mimalloc's option plus `lockpriv`, so it must be computed in the process whose pages it describes.
- **church_bv changes:**
  - `machine::machine_state()` calls `state::line()` and adds `pages`.
  - The `CPU=` field keeps its meaning at both ends: a 2 s sample at the time of the line, not the run's average. That is a 2 s wait, but no process and almost no CPU.
  - The driver composes its lines itself:
    - `RTP` and `CPU` are machine-wide, so it reads them in its own process.
    - Only `lockpriv` and `pages=` belong to the children's process and environment, so it gets those through a worker task, `machine::pages_line`, which replaces `machine_state_line` in the driver's task table. That task prints `pages: lockpriv=<bool> pages=<large|normal>` and takes milliseconds.
    - The driver's line stays `machine at <when>: machine state: RTP=.. CPU=..% lockpriv=.. pages=..`, so the `machine at` greps in docs and scripts keep matching.
  - Names that stay: `machine::machine_state()`, which now calls `state::line()` and adds `pages`, so `.cargo/config.toml`'s comment stays right. `machine_state_line` also stays, as a test printing the whole line, for a human.
  - `MACHINE_STATE=0` keeps skipping both lines. `runs gate` and `runs time --sweep` set it, since `runs` records the machine itself.
  - The stale comment naming `scripts/loop_stream.sh` (gone, now `driver::loop_stream`) is corrected.

## Commands

All of them print progress to stdout as they go, and write their records under the run directory.

- **`runs dir`:** prints and creates this checkout's run directory, `%TEMP%\tatic-runs\<checkout folder>`.
  - The checkout is the one the running `runs.exe` was built in: the nearest folder above `std::env::current_exe()` that holds `tools/runs/Cargo.toml` (four levels for `<checkout>/tools/runs/target/release/runs.exe`, five for a test exe in `target/debug/deps`).
  - This is `kk.sh`'s rule. `kk.sh` follows its own script's checkout (`git -C <script dir>`), not the current directory, so a tool built in a worktree writes to that worktree's run directory wherever it is called from.
  - The exe's location is used instead of git, so `runs` works from any directory without git on PATH.
  - Placeholders and paths are printed in Windows form, with long names. `%TEMP%` can be an 8.3 short path (`WINSTO~1`), so it is expanded with `GetLongPathNameW`. The `kk.sh` agreement test compares both directories after that normalization.
- **`runs run <dir> [--affinity M] [--priority P] -- [VAR=val]... <exe> <args>...`:** one measured run.
  - stdout goes to `<dir>/out.txt` and stderr to `<dir>/err.txt`.
  - It prints one result line, in the format below, and exits with the run's exit code, as `pin.ps1` did. This replaces `sweep_job.ps1` and `pin.ps1`.
- **`runs time <dir> --rounds N [--max-hours H] [--others pat,...] [--foreign-max 20] [--quiet-secs 60] [--keep-dirty] [--max-rounds R] [--grep NAME=REGEX]... [--affinity M] [--priority P] -- <arm> [-- <arm>]...`:** alternating timing. The presets `--sweep` and `--pcs` (below) stand in for the arms.
  - **Arms:** each arm is `<name> [VAR=val]... <exe> <args>...`. After the name, every token matching `^[A-Za-z_][A-Za-z0-9_]*=` is environment, up to the first token that does not match, which is the exe.
  - **Defaults:** `--max-hours 3`. `--quiet-secs 0` skips the quiet wait.
  - **`--keep-dirty`:** for a machine that is never quiet, as `cpu_ab.ps1` and `cpu_arms.ps1` ran at 61-85% load. Every round counts toward N and is recorded with its clean flag, and the summary reports clean rounds and all rounds separately. Without it, `--max-rounds` (default 4N) caps the attempted rounds, so a loaded machine ends the timing instead of running out the deadline.
  - **A fresh directory:** `time` refuses a `<dir>` that already holds `runs.tsv`, whose old rows would mix into the count (`ab.sh` refuses for the same reason), and deletes a stale `<dir>/stop` at the start.
  - **Placeholders:** `{r}` (round), `{arm}` and `{dir}` in arguments and values are substituted. For example `SWEEP_OUT={dir}/{arm}.{r}` gives each run its own output.
  - **Order:** round r (from 1) runs the arms rotated left by r-1. Two arms go AB in round 1, then BA, as `ab.sh` and `hc_rounds.ps1` start; more arms rotate, as `cpu_arms.ps1` does.
  - **`--grep NAME=REGEX`** (repeatable): the first capture group of the last line of each run's output that matches REGEX becomes column `NAME` in `runs.tsv` and in the summary. Example: `--grep 'check=^COST rule-proofs:.* check=([0-9.]+)ms'` for the check time in `proof_cost_split`'s `COST rule-proofs: n=.. build=..ms check=..ms ...` line (search.rs:2106), whose `build=` and `check=` `cpu_ab.ps1` printed. The `--pcs` preset greps both.
  - Ruling: `cpu_ab.ps1` took the first matching line; `--grep` takes the last. It matters only if a line repeats, and `proof_cost_split` prints `rule-proofs` once.
  - **Waiting for quiet:** before each round, wait until the last `--quiet-secs` of 2 s samples show machine load under `--foreign-max` and no other jobs' processes. The wait checks after every sample (`ab.sh` checked every 10 s) and stops at the `--max-hours` deadline or when `<dir>/stop` exists. These are the waits and stop rules `quiet_ab` has. The wait samples in the main thread, since nothing runs during it; during a run, `runs::job`'s sampler thread watches for others' processes.
  - **Clean runs:** a run is clean when its exit code is 0, the other processes' load during it is under `--foreign-max`, and no other job's process appeared. A round is clean when all its arms are.
  - **When it stops:** at N clean rounds (N rounds of any kind with `--keep-dirty`), `--max-rounds` attempted rounds, the deadline, `stop`, or a failed run. A failed run stops the timing, as `quiet_ab` does: it would only fail again.
  - **Machine state:**
    - `state::line()` is logged at the start and the end of the timing, to stdout and to `<dir>/state.txt`, so `lockpriv` is on record as the sweep's `machine at` line had it.
    - `rtp` is also read before each round: milliseconds while the service is stopped, about 1 s while it runs, including when the service runs with protection toggled off. A change is logged.
    - The `pages=` of a sweep's children is not visible to `runs`. With `MIMALLOC_ALLOW_LARGE_OS_PAGES=0` in the arms it is `normal` by construction. Otherwise the arm's own output has it, if the exe prints it.
  - **Completion:** the last line of `runs.tsv` is followed by `<dir>/done.txt`, holding `done <clean rounds>/<rounds> <why it stopped>`, so a background timing can be watched for it (as for `hc_rounds ALL`).
  - **Records:**
    - `<dir>/runs.tsv`: one row per run, written as it ends. Columns: arm, round, position, start unix seconds, wall s, job CPU s, processes, stragglers, peak process MB, peak job MB, other load %, other jobs' processes, rtp, exit code, clean, then the `--grep` columns.
    - `<dir>/<arm>.<r>.out.txt` and `.err.txt`: each run's output.
    - `<dir>/summary.txt`: per arm, over clean rounds, the median and best job CPU and wall. Per arm against the first arm: the paired differences per clean round and how many rounds it won.
  - **`--sweep <old exe> <new exe>`:** expands to the two arms `old` and `new`, each `MACHINE_STATE=0 SALT=1 SWEEP="mines own cold pooled" MIMALLOC_ALLOW_LARGE_OS_PAGES=0 SWEEP_OUT={dir}/{arm}.{r} <exe> driver::sweep --exact --ignored --nocapture`, with `--rounds 6` unless given. This is `hc_rounds.ps1`'s experiment with the checks moved out of the job; `hc_rounds.ps1`'s fixed twelve runs become six clean rounds of two.
  - **`--pcs <exe> [<new exe>]`:** `cpu_ab.ps1`'s and `cpu_arms.ps1`'s experiment. Arms of `CHECK_FAMILY=cmp3d CHECK_RULES=<scripts dir>/cmp3d_own_rules.txt RULEMINER_LAWS=300 <exe> search::proof_cost_split --exact --ignored --nocapture`, with `--grep` on its `COST` line. `<scripts dir>` is `<checkout>/docs/runs/2026-10-12/scripts`, the checkout found as `runs dir` finds it.
    - With one exe, further `--arm-env NAME:VAR=val,...` options define the arms that differ in environment. An arm without variables is `NAME:`.
    - With two, the arms are `old` and `new`.
    - So the recipe that about 15 rows of the run log cite as "`cpu_ab.ps1`'s environment" stays runnable, and is written once.
    - `cpu_arms.ps1`'s peak working set and peak private bytes become the job's peak process and peak job commit. Working set is dropped: no conclusion used it.
- **`runs gate <tag> <old exe> <new exe>`:**
  - It first deletes the four `<run dir>/<tag>_<arm>_<salt>` directories and `<tag>_gate.txt`, so a reused tag starts clean, as `hc_seq.sh`'s `rm -rf` and `sed -i` did.
  - It runs four sweeps with `runs::job` into those directories, in `hc_seq.sh`'s order: new 1, old 1, old 2, new 2.
  - A sweep that exits nonzero stops the gate with `<tag> FAILED`.
  - Each sweep is `MACHINE_STATE=0 SWEEP_OUT=... SALT=<s> SWEEP="mines own cold pooled" <exe> driver::sweep --exact --ignored --nocapture`, at the default priority and affinity (BelowNormal, `0xFFF`, as `hc_seq.sh`'s `start` had), with stdout and stderr both in `log.txt`, as `hc_seq.sh`'s `> log.txt 2>&1` does.
  - Each line printed is `<tag> <arm> <salt> <wall>s cpu=<s>`. It is also appended to `<run dir>/<tag>_gate.txt`. Then it runs `runs cmp <tag>`, printing its lines and writing them to `<run dir>/<tag>_cmp.txt`, and appends `<tag> cmp same` or `<tag> cmp differs`, then `<tag> ALL`. So `<tag>_gate.txt` ends with `<tag> ALL` (verdict on the line before) or `<tag> FAILED <why>`, and a background gate can be watched as `hc_done.txt` was, with the verdict already there. The gate exits nonzero if a sweep failed or any `cmp` line other than `salt <s>: same file list (..)` and `cmp done` appeared.
  - So `DIFF`, `(order only)`, `ERROR` and the file-list lines `< f` (only in old) and `> f` (only in new) all fail it. In `gate_cmp.py` a file only the new side has prints just `> f`, which a check for `DIFF` alone would miss.
  - An `(order only)` difference that a change is known to tolerate is judged by a human from the output, as now.
- **`runs cmp <tag> [--dir D]`:** `gate_cmp.py` ported line for line.
  - It has the same normalization: the `CUT` table; timings to `T`; `<tag>_(old|new)` to `RUN`; `N filtered out`; libtest's harness lines dropped in `.txt` and `.log`.
  - It has the same output format, including `(order only)`, and the same file walk order (sorted `./`-relative paths with `/`).
  - The run directory defaults to `runs dir`.
  - One intended difference: a missing `<tag>_<arm>_<s>` directory prints `ERROR salt <s>: listing failed (..)`. `gate_cmp.py` meant to (its `try`), but `os.walk` ignores a missing directory, so it printed `same file list (0 files)` and a gate on a missing run would pass. The `ERROR` line for a file that cannot be read keeps its form; only the OS error text inside the parentheses differs from Python's.
- **`runs state`:** prints `state::line()`, for a human or a script before or after anything.

### The result line

`run` prints, and `time` logs to stdout, one line per run:

`<label> wall=<s>s jobcpu=<s>s procs=<n> stragglers=<n> peakproc=<MB>MB peakjob=<MB>MB other=<%>% others=<n> rtp=<True|False|?> exit=<code>`, with the units written as `sweep_job.ps1` wrote them (`wall=12.3s jobcpu=10.41s peakproc=279MB`).

- **Dropped from `sweep_job.ps1`'s line:** `kernel=` and `faults=`. The kernel split is unreliable here (LONG_RUNS.md), and faults were never used in a conclusion. Ruling; cost if wrong: one field back.
- **Different baseline:** `sweep_job.ps1`'s job held its own PowerShell. So its `procs` was one higher, and its `peakjob` included that PowerShell's commit (the machine-state PowerShells too). Numbers from the two tools are not compared directly.

## Testing (in `tools/runs`, `cargo test --manifest-path tools/runs/Cargo.toml`)

- **`cmp` on synthetic runs:** `gate_cmp_check.sh`'s four files on two salts give its exact expected output. A missing file on one side gives `< f` and `> f` lines. A `.tsv` cut drops the right field, and keeps a line without tabs whole.
- **`cmp` equivalence, one-off (in the plan, not a unit test):** `runs cmp` against `gate_cmp.py` on `bfs` and on a recreated cross-salt `xs` pair gives byte-identical output. Only then is `gate_cmp.py` deleted.
- **Job accounting:** `run` on `cmd /c` starting a child that busy-loops for about 0.5 s (the test exe itself, `std::env::current_exe()`, re-run with an `#[ignore]`d test that spins; no extra binary ships) gives `procs >= 2` and job CPU at least 0.4 s. So children are counted.
- **Kill on close:** a run whose child sleeps 60 s; dropping the job handle early ends the child within a deadline. The child's exit is polled on a deadline, with no fixed sleep.
- **Rotation:** rounds 1-4 with three arms give ABC, BCA, CAB, ABC; with two arms, AB, BA.
- **Relative exe and `current_dir`:** `run` with a relative exe path and a different `current_dir` starts the right exe (`test_clean.sh`'s pin case).
- **Environment removal:** an arm with `VAR=` does not see a `VAR` set in `runs`'s own environment.
- **Stragglers:** a main process that exits while its child lives on is reported with the child's CPU counted, after the wait.
- **`time` bookkeeping:** `--grep` takes the last matching line; a `<dir>` holding `runs.tsv` is refused; `done.txt` follows the last row; `--max-rounds` ends a timing whose rounds are all dirty (the cleaning rule fed a fake load).
- **Gate verdict:** the exit code is nonzero for a synthetic pair with only a `> f` line.
- **Cleaning rule:** `test_clean.sh`'s cases as a pure function: total busy, own CPU, wall and processors give the other-load percentage; a run with an others' process is dirty; a failed run is dirty.
- **`dir` against `kk.sh`:** when bash is on PATH, the two give the same directory.
- **`state`:** `line()` has the three fields, and `rtp` is `Some(_)` on this machine. A unit test of the status-flag decision uses a fake buffer (bit 0 set gives `Some(false)`; bit 0 clear means fall back).
- **church_bv:** `machine_state_line` still prints `machine state: ... pages=...`. `mimalloc_defaults_to_large_pages` is unchanged.
- **One-off checks against today's tools (in the plan):**
  - **Job CPU:** three `runs run` sweeps of `bf_sweep.exe` against three `sweep_job.ps1` sweeps of the same exe, all with `MACHINE_STATE=0` in the environment (`sweep_job.ps1` passes it through). Job CPU should agree within the run-to-run spread, allowing for the launcher PowerShell `sweep_job.ps1` counts. `bf_sweep.exe` is current code, so it honours `MACHINE_STATE`.
  - **`pin.ps1`:** `runs run` against `pin.ps1` on one `proof_cost_split`, the same way.
  - **`sweep_xperf.ps1`:** it needs elevation, so it is checked by hand once by the user, after its edit, and the plan says so.

## Docs to update

A grep for every deleted name runs before the deletion commit, outside `target/` and `.claude/`. Current-practice mentions are updated; mentions in historical records (old run-log rows, RELATED_WORK.md sections, plans and specs) stay, since they say what ran then.
- **README:**
  - Requirements: the `pin.ps1` example becomes `runs`.
  - The `quiet_ab` paragraph, which also names `clean.py` and `test_clean.sh`, becomes `runs time`.
  - Quick start: the `runs` build line.
- **docs/tier-cycle.md:**
  - Around line 509, "Speed claims in this file should come from `quiet_ab` runs" becomes `runs time`. The `pin.ps1` sentences there (507-509) are history and stay.
  - Around line 3094, where `cpu_ab.ps1` and `sweep_job.ps1` are named as the current method, the current method becomes `runs time --pcs` and `runs run`.
  - The workflow-survey entry records that `runs` was built, and what it measured.
- **docs/runs/2026-10-12/README.md:**
  - The header, line 11, names `kk.sh` and `kk.ps1`; it becomes `kk.sh` and `runs dir`.
  - The header names `runs` for new rows; old rows keep the script names they ran with.
- **`.cargo/config.toml`'s comment:** it names `machine::machine_state`, which stays; no change.

## Deleted

After the equivalence checks above:
- `hc_seq.sh`, `gate_cmp.py`, `gate_cmp_check.sh`, `hc_rounds.ps1`, `sweep_job.ps1`, `cpu_ab.ps1`, `cpu_arms.ps1` and `kk.ps1`, from `docs/runs/2026-10-12/scripts`;
- the whole `scripts/quiet_ab/`;
- the PowerShell in `machine.rs`.

`cmp3d_own_rules.txt` stays: it is the data `runs time --pcs` reads.

## Not decided here

- **`runs time` on a GPU job.** Leases (LONG_RUNS.md) are not part of this. None of the replaced scripts handled them, and no sweep uses the GPU.
- **Profiling.** samply stays with `profile.ps1`, which needs the elevated task.
