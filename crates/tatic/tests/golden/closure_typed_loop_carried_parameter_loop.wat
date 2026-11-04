(module
  (type $ty1 (func (param i32) (param i64) (result i64)))
  (table 2 funcref)
  (elem (i32.const 0) $c0 $c1)
  (func $c0 (param $env i32) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)
    (local $t0 i64)
    (local $t1 i64)
    (local $t2 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      local.get $p0
      i64.const 0
      i64.le_s
      if (result i64)
        local.get $p2
      else
        local.get $p0
        i64.const 1
        i64.sub
        local.set $t0
        local.get $p1
        local.set $t1
        local.get $p1
        i64.const 32
        i64.shr_u
        i32.wrap_i64
        local.get $p2
        local.get $p1
        i32.wrap_i64
        call_indirect (type $ty1)
        local.set $t2
        local.get $t0
        local.set $p0
        local.get $t1
        local.set $p1
        local.get $t2
        local.set $p2
        br $L
      end
    )
  )
  (func $c1 (param $env i32) (param $p0 i64) (result i64)
    (local $t0 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      local.get $p0
      i64.const 1
      i64.add
    )
  )
  (func $f (result i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      i32.const 0
      i64.const 150
      i32.const 0
      i64.extend_i32_u
      i64.const 32
      i64.shl
      i64.const 1
      i64.or
      i64.const 0
      call $c0
    )
  )
  (export "f" (func $f))
)
