## 43. How other compilers call a closure of unknown arity

§40's hole comes from `Dispatch::Fast` assuming a call site's argument
count is the callee's arity, unchecked. No compiler surveyed here does
that. Each one either checks at runtime at a call to an unknown function,
or shows statically that there is no such call.

**Checking at runtime (eval/apply).**
- **GHC** (Marlow and Peyton Jones, "Making a fast curry"): a call to a
  known function with enough arguments is direct. A call to an unknown
  one goes through generic apply routines that read the closure's arity.
  If it matches, they jump in. If there are fewer arguments, they build a
  PAP. If there are more, they call with that many and apply the result
  to the rest.
- **OCaml:** a closure records its arity. An unknown call with `n`
  arguments goes through `caml_applyN`, which takes the full-application
  entry point when the arity is `n` and otherwise applies one argument at
  a time. Flambda 2 names the cases (`call_kind.mli`: direct, indirect of
  known arity, indirect of unknown arity). wasm_of_ocaml does the same on
  WASM, with an arity field in the closure.
- **Lean 4:** the IR separates `fap` (a full call of a known constant),
  `pap` and `ap`. `ap` goes through `lean_apply_n`, which checks the
  closure's stored arity (Ullrich and de Moura).

**Showing it statically.**
- **MLton:** closure conversion is directed by whole-program flow
  analysis (0CFA). A function value becomes a variant of a sum type
  naming which function it is, so every call is to a known function, and
  coercions are inserted between representations (Cejtin et al.). This
  needs the whole program, which a JIT compiling one term at a time
  doesn't have for a parameter.
- **GHC, again:** its Core optimiser eta-expands functions to the arity
  their uses need, so more calls take the fast path. Call Arity
  (Breitner) does this from how a function is used, not how it is
  defined. Downen et al. make it type-directed: extensional function
  types make eta-expansion always valid ("Making a faster curry with
  extensional types"), and arity in kinds makes the calling convention
  part of the type ("Kinds are calling conventions").

**What that means for tatic.** Three responses were surveyed after §42:
1. **A runtime check** (1a). Keep `Fast`, but check the stored arity at
   each unknown call and fall back to the curried path on a mismatch.
   This is the mainstream answer, and what §9 concluded a closure of
   genuinely unknown origin needs: a uniform calling convention or
   adapters. It makes the compiled code correct but earns no universal
   proof, since the kernel's `Clo_k` is arity-exact and curried dispatch
   gets only per-sample proofs. So such terms would still be declined.
2. **An eta rewrite** (1b), GHC's Core-level answer. Rewrite the term
   before compiling so that arities agree, e.g. pass `\x. (\y. clo x y)`
   where a one-argument function is expected, with a certificate that the
   rewrite preserves meaning (as `spec_check` does for the specialiser).
   Eta on a lambda value is sound under call-by-value. It is the only
   option that turns declines into installs, since the existing provers
   apply to the rewritten term.
3. **A static arity check** (1c), the Kinds paper without the rewrite.
   It is cheap and independent of the proof gate, but gains nothing while
   the proof gate already declines these terms.

None is done. The main run declines no term for want of a proof, so
nothing in the corpus needs them yet. If one is, 1b fits the proof-gated
design best, and 1a remains the eventual fix for closures of unknown
origin.

