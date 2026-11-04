(module
  (func $f (param $p0 i64) (result i64)
    (local $t0 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      local.get $p0
      i64.const 0
      i64.le_s
      if (result i64)
        i64.const 0
      else
        local.get $p0
        i64.const 8
        i64.mul
        i64.const 0
        i64.add
        local.get $p0
        i64.const 1
        i64.sub
        call $f
        i64.add
      end
    )
  )
  (export "f" (func $f))
)
