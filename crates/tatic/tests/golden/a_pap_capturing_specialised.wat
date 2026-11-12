(module
  (func $f (param $p0 i64) (result i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    i64.const 3
    i64.const 4
    i64.add
    local.get $p0
    i64.add
  )
  (export "f" (func $f))
)
