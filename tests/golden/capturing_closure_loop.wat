(module
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
  (table 1 funcref)
  (elem (i32.const 0) $c0)
  (func $c0 (param $env i32) (param $p0 i64) (result i64)
    (local $t0 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      local.get $env
      i64.load offset=0
      local.get $p0
      i64.add
    )
  )
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
        i32.const 8
        call $alloc
        local.set $envtmp
        local.get $envtmp
        local.get $p1
        i64.store offset=0
        local.get $envtmp
        local.get $p0
        call $c0
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
