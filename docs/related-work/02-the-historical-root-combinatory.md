## 2. The historical root: combinatory logic

Curry/Schönfinkel's combinatory logic (1920s-30s) predates λ-calculus:
no variables or binders at all, every term built from fixed-arity
combinators (`S`, `K`, `I`) composed purely by application. Illative
combinatory logic (Curry's later extension, folding logical connectives
in as combinators) ran straight into Curry's paradox — an early, hard
lesson that "just add application" needs real stratification discipline
to stay consistent, directly prefiguring why tatic's own kernel is
predicative rather than naively unrestricted.

Worth noting for vocabulary alone: tatic's own `Combinators`/`register`
naming (`src/compile.rs`, `src/proof.rs`) echoes this lineage — a
"combinator" here, as there, is a fixed-arity building block whose
identity and shape are pinned at construction time, composed by
application, never partially-evaluated into some more general closure
form.

