(module
  (type $ty1 (func (param i32) (param i64) (result i64)))
  (memory 1)
  (global $hp (mut i32) (i32.const 0))
  (func $alloc (param $n i32) (result i32)
    (local $base i32)
    (local $need i32)
    global.get $hp
    local.set $base
    local.get $base
    local.get $n
    i32.add
    local.set $need
    local.get $need
    memory.size
    i32.const 65536
    i32.mul
    i32.gt_u
    if
      local.get $need
      memory.size
      i32.const 65536
      i32.mul
      i32.sub
      i32.const 65535
      i32.add
      i32.const 65536
      i32.div_u
      memory.grow
      drop
    end
    local.get $need
    global.set $hp
    local.get $base
  )
  (export "hp" (global $hp))
  (export "memory" (memory 0))
  (table 3 funcref)
  (elem (i32.const 0) $c0 $c1 $c2)
  (func $c0 (param $env i32) (param $p0 i64) (result i64)
    (local $t0 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      i32.const 0
      i64.extend_i32_u
      local.get $p0
      i32.const 16
      call $alloc
      local.set $envtmp
      local.set $papenv
      local.get $envtmp
      local.get $papenv
      i64.store offset=8
      local.set $papenv
      local.get $envtmp
      local.get $papenv
      i64.store offset=0
      local.get $envtmp
      i64.extend_i32_u
      i64.const 32
      i64.shl
      i64.const 2
      i64.or
    )
  )
  (func $c1 (param $env i32) (param $p0 i64) (param $p1 i64) (result i64)
    (local $t0 i64)
    (local $t1 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      local.get $p0
      i64.const 10
      i64.mul
      local.get $p1
      i64.add
    )
  )
  (func $c2 (param $env i32) (param $p0 i64) (result i64)
    local.get $env
    i64.load offset=0
    i32.wrap_i64
    local.get $env
    i64.load offset=8
    local.get $p0
    call $c1
  )
  (func $f (result i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      i32.const 0
      i64.const 5
      call $c0
      i64.const 32
      i64.shr_u
      i32.wrap_i64
      i64.const 3
      i32.const 0
      i64.const 5
      call $c0
      i32.wrap_i64
      call_indirect (type $ty1)
    )
  )
  (export "f" (func $f))
)
