// rc_probe.rs (g2, 2026-11-11): the closure loop's specialised body as `return_call` against `loop` on a default
// wasmtime Engine; best of 30 per n, and each module serialized to $PROBE_OUT for llvm-objdump. To run, copy it to
// crates/tatic/examples/ and `PROBE_OUT=<dir> cargo run --release -p tatic --example rc_probe`.
use std::time::Instant;
const RC: &str = r#"(module (func $f (export "f") (param $p0 i64) (param $p1 i64) (result i64)
  local.get $p0 i64.const 0 i64.le_s
  if (result i64) local.get $p1
  else local.get $p0 i64.const 1 i64.sub local.get $p1 local.get $p0 i64.add return_call $f end))"#;
const LP: &str = r#"(module (func $f (export "f") (param $p0 i64) (param $p1 i64) (result i64)
  (local $t i64)
  loop $top (result i64)
    local.get $p0 i64.const 0 i64.le_s
    if (result i64) local.get $p1
    else local.get $p0 i64.const 1 i64.sub local.get $p1 local.get $p0 i64.add
      local.set $p1 local.set $p0 br $top end
  end))"#;
fn main() {
    let out = std::env::var("PROBE_OUT").unwrap();
    let engine = wasmtime::Engine::default();
    for (name, wat) in [("rc", RC), ("loop", LP)] {
        let m = wasmtime::Module::new(&engine, wat).unwrap();
        std::fs::write(format!("{out}/{name}.cwasm"), m.serialize().unwrap()).unwrap();
        let mut store = wasmtime::Store::new(&engine, ());
        let i = wasmtime::Instance::new(&mut store, &m, &[]).unwrap();
        let f = i.get_typed_func::<(i64, i64), i64>(&mut store, "f").unwrap();
        for n in [20_000i64, 2_000_000] {
            let mut best = f64::MAX;
            for _ in 0..30 {
                let t = Instant::now();
                let r = f.call(&mut store, (std::hint::black_box(n), 0)).unwrap();
                best = best.min(t.elapsed().as_secs_f64());
                assert_eq!(r, n * (n + 1) / 2);
            }
            println!("{name} n={n} best {:.3} us  {:.3} ns/iter", best * 1e6, best * 1e9 / n as f64);
        }
    }
}
