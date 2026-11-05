## 8. Quantitative Type Theory — usage tracking, not arity tracking

QTT (Idris 2, Granule) extends dependent types with per-binder usage
multiplicities (0 = erased, 1 = linear, ω = unrestricted), checked as
part of typing. Tangential to tatic's own concerns (it tracks *how many
times* an argument is used, not *how many arguments* a function takes),
but flagged during the arity-polymorphism scoping pass as a reminder that
"track an extra dimension of a value's usage/shape in the type" is itself
an established, actively-used 2020s technique — relevant framing for
anyone re-approaching the arity-tracking problem in §9.

