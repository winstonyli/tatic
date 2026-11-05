## 7. Homotopy Type Theory / Cubical Type Theory — the maximal end of the same axis

Equality as genuine structure (a path/identification), the univalence
axiom, cubical type theory (2015-on) giving it real computational content
via an interval type and Kan composition. Very active currently — 2024-25
work spans "higher observational type theory" (folding OTT ideas back
into HoTT), formalized synthetic-homotopy results in Cubical Agda, and
explicit unifications of cubical with guarded/multimodal type theory
(§3) into one framework. `Id` in `src/kernel.rs` is deliberately the
un-cubical, non-univalent Martin-Löf identity type — this tier represents
what tatic's kernel is *not* trying to be, on purpose: the goal here is
compositional-structure proofs about one specific compiler, not synthetic
homotopy theory.

