(module
  (type $ty1 (func (param i32) (param i64) (result i64)))
  (func $f (param $p0 i64) (param $p1 i64) (result i64)
    (local $t0 i64)
    (local $t1 i64)
    (local $envtmp i32)
    (local $papenv i64)
    (local $diva i64)
    (local $divb i64)
    (loop $L (result i64)
      local.get $p0
      i64.const 32
      i64.shr_u
      i32.wrap_i64
      local.get $p0
      i64.const 32
      i64.shr_u
      i32.wrap_i64
      local.get $p1
      local.get $p0
      i32.wrap_i64
      call_indirect (type $ty1)
      local.get $p0
      i32.wrap_i64
      call_indirect (type $ty1)
    )
  )
  (export "f" (func $f))
)
