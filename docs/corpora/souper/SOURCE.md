# souper

- **Source:** `github.com/google/souper`, commit `963d4df436f3dc0b039cc0e47ada0577a26f5c4e` (checked 2026-11-01), directory
  `test/Infer`, subdirectories `HackersDelight`, `syn-const`, `syn-double-insts`, `syn-single-inst` (39 files, 15,502 bytes).
  Raw files are kept outside the repo, in `%LOCALAPPDATA%\corpora-raw\souper\`.
- **Licence:** Apache-2.0 (the repo's licence file at that commit). Only short expressions are translated here.
- **Format:** `cases.txt`, `name<TAB>term`, name = `<subdir>/<file>`. Each file's `infer` target is the expression; the
  rest (RUN/CHECK lines, the synthesised right-hand side) is dropped. Translation: Souper's `1` is `sub(0, -1)` (written
  literally, so the table's job is visible); `lshr %x, 1` is `shr1(x, 0)`; i1 results are 0/1 words.
- **In scope: 14 of 39 files.** The term language has `add sub and or xor lt shl1 shr1`, constants 0 and -1, no `mul`, no
  select/eq, no width-specific shifts, and one width.
  - HackersDelight (14 files): P1 to P7, P10 to P12, P14, P15, P17 in scope (13). P9 out (`ashr 31`: width-specific).
    `ule(a, b)` is `xor(lt(b, a), 1)` and `ult` is `lt` (unsigned, 0/1); P10 and P12 first panicked the measurement
    (`abstract_atoms` did not treat `lt` as an atom), fixed 2026-11-01.
  - syn-const (3): `const1` in scope (`x + 1 + 1`). `const2` (shl/lshr by 8), `issue616` (`uadd.sat`, i234) out.
  - syn-double-insts (8): all out: `ctpop`, `mul` (three files, including `two-constants`), `freeze`, i1 `select`/`eq`
    (`nand`), `sext`/`slt` (`sadd-overflow`), `urem`/`select`/`trunc` (`trunk-insertion`).
  - syn-single-inst (14): all out: `trunc`/`sext`/`zext`, `sdiv`, `freeze`, `fshl`/`fshr`, `select`, the saturating
    arithmetic files (`mul`/`select`/`*.with.overflow`), the path-condition `pc` (`div-shr`, `ub`), `ub` (`shl` by a
    variable), `large-lhs` (`ctpop` with 32-bit mask constants and shifts by 2, 4, 8, 16), `sub` (`add`/`sub` of the
    constant 10, which the term language cannot name; only 0 and -1 exist).
- **Measure:** `CORPUS=docs/corpora/souper/cases.txt cargo test --test church_bv --release corpus_report -- --ignored --nocapture`.
  Result (2026-11-01): 14 cases, 52 operators; the table changes 10 and leaves 42; the base rewriter also leaves 42.
  Overlap with `hd-own`: P1 to P7, P14 and P15 are the same routines as there, written with Souper's `sub x 1`.
