## 6. Observational Type Theory / Setoid Type Theory — equality without the heavy machinery

An alternative to HoTT/cubical for function extensionality and
well-behaved equality: define equality by recursion on type structure
("what would make two functions/pairs/etc. equal") rather than an
inductively-generated identity type with an axiom bolted on. Another
"honest, minimal postulate" design in the same spirit as tatic's own
`Id`-typed axioms — a useful reference point for anyone tempted to reach
for cubical machinery here later: it usually isn't necessary for what
this project actually needs from equality (compositional-structure
agreement between two readings of a term, not synthetic mathematics).

