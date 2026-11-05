## 76. Search-guided rewriting: what prior systems verify, and what guides them

Surveyed 2026-09-30 from search-result summaries only (no paper was read in full, so every line is a pointer to check, not a finding).

- **STOKE** (Schkufza et al.): MCMC search over x86-64 programs with a cost function that combines correctness and speed. It has equivalence checking from tests, through bounded verification, to fully formal verification. Search is stochastic and unguided by a learned model; the checker is what makes results trustworthy. Same split as `specialise.rs` / `spec_check.rs`.
- **AlphaDev** (DeepMind, Nature 2023): reinforcement learning plays an "assembly game", adding one instruction at a time, rewarded for correct and fast sorts; results reached LLVM libc++. The summaries found do not say how correctness is checked; not verified here, so do not cite it as a proof-producing system.
- **egg** (POPL 2021): equality saturation with e-graphs, rebuilding, and e-class analyses. The non-learned baseline for rewrite-order search: it applies all rules and extracts the cheapest term, which sidesteps phase ordering.
- **Learned guidance for equality saturation** (2023 to 2025 workshop and arXiv papers): MCTS over e-graph construction (MCTS-GEB), LLM-proposed rewrite checkpoints with e-graphs filling the gaps (LGuess), and rule-phase ordering from a dependency graph. Titles and one-line abstracts only.

What it means here. Every system that scales keeps the checker separate from the search, as this repo does. The non-learned baseline (egg-style saturation plus a cost table) is the thing to measure first. The census in the bit-vector design doc (section 14) shows the corpus has almost no matches for the first three rules, so a learned guide has nothing to learn from until a benchmark with real rewrite opportunities exists. Not surveyed: learned proof search in proof assistants (the lemma-proving half).

