(module
  (table 1 funcref)
  (elem (i32.const 0) $c0)
  (func $c0 (param $e0 i64) (param $p0 i64) (result i64)
    (local $t0 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      local.get $e0
      local.get $p0
      i64.add
    )
  )
  (func $f (param $p0 i64) (result i64)
    (local $t0 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      local.get $p0
      i64.const 5
      call $c0
    )
  )
  (export "f" (func $f))
)
