## 78. Can normalization be eased? Explicit conversion, proof irrelevance, observational, cubical, categorical views

Searched 2026-09-30. Abstract or search-summary level only (the OTT paper's PDF could not be parsed here); every line is a pointer to check.

- **Explicit conversion** (nLab "explicit conversion"): conversions become terms `p : a = b` instead of a judgment `a == b`. The nLab page does not discuss proof size or decidability.
- **Eliminating reflection from type theory** (Winterhalter, Sozeau and Tabareau, CPP 2019): extensional type theory (equality reflection, undecidable checking) is translated to intensional type theory with UIP and funext, turning each use of reflection into an explicit equality proof. This moves the conversion work into the proof term; it does not remove it.
- **Observational type theory** (Altenkirch, McBride and Swierstra, PLPV 2007): equality is defined by recursion on the type; it is proof-irrelevant and substitutive, while definitional equality stays decidable as in ITT (search summary).
- **Definitional proof irrelevance without K** (Gilbert, Cockx, Sozeau and Tabareau, POPL 2019): all proofs of a proposition are definitionally equal, so conversion need not compare or normalise proofs; a criterion on which propositions may be eliminated keeps checking decidable and compatible with univalence.
- **Cubical type theory** (Sterling and Angiuli, LICS 2021): normalization was the last major open metatheory problem; proved by a reduction-free gluing argument, giving decidable judgmental equality. Cubical adds computation (Kan operations) for univalence and funext, so it makes normalization larger, not smaller.
- **Two-level type theory** (Annenkov, Capriotti, Kraus and Sattler, 2023): an inner fibrant (HoTT) level and an outer level with UIP whose equality is internalised judgmental equality.
- **Categories with families and NbE** (Altenkirch and Kaposi, LMCS 2017): substitution is a primitive of the syntax; NbE is extracted from a presheaf model with no rewriting.

What it means here. No line of work removes normalization while keeping decidable checking of computing terms: they either move it into proofs (explicit conversion, reflection elimination), skip it for proofs (proof irrelevance, OTT), make it cheaper (closures and NbE, from the CwF view where substitution is explicit), or enlarge it (cubical). The bit-vector lemma's cost is conversion over computational terms (`add`), which only the third route touches.

