(module
  (func $f (param $p0 i64) (param $p1 i64) (result i64)
    (local $t0 i64)
    (local $t1 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      local.get $p0
      i64.const 0
      i64.le_s
      if (result i64)
        local.get $p1
      else
        local.get $p0
        i64.const 1
        i64.sub
        local.set $t0
        local.get $p1
        local.get $p0
        i64.add
        local.set $t1
        local.get $t0
        local.set $p0
        local.get $t1
        local.set $p1
        br $L
      end
    )
  )
  (export "f" (func $f))
)
