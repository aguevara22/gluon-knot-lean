# Selected-cut refinement: independent technical review

Reviewer: root. Implementer: /root/review_contraction_candidates. Root did not
author this body. This is same-model technical review, not stronger fidelity
approval or source acceptance.

Scope: the13 declarations in SelectedCutRefinement, especially the exact
arbitrary-selected-cut reindexing and full summand factorization needed in
source pf:formal-cancellation. Root read the body and relevant canonical APIs,
then ran the exact prototype in kernel32831 (exit0). All13 printed axiom traces
use only propext, Classical.choice and Quot.sound.

The outer raw composition represents selected positions exactly by
selectedComposition_interior; endpoint containment is equivalent to containment
of those interior positions. The refining-composition equivalence and existing
ordered flatten/unflatten preserve the actual physical cuts. prod_inner_positions
uses the established unmarked-index correspondence, so a selected cut cannot
also occur as an inner cut. prod_refined_children supplies all actual children,
not merely their lengths or an abstract product. The complete termwise identity
therefore reindexes both cut weights and child coordinates. Fintype.prod_sum
and the genuine equivalence give the factorization of finite sums.

Quantification is over every outer composition and every inner family. Empty
selected sets, unary inner compositions, one-leaf gaps and zero weights remain
included. The selected scalar exponent is exactly the physical interior-set
cardinality. No division, arity restriction, geometric premise, hidden
bijection certificate or desired coefficient identity is assumed. No defect
found within this scope. The polynomial coefficient identification, geometric
gap specialization and actual cancellation remain separate obligations.

Evidence bindings:

| File | SHA-256 |
| --- | --- |
| `work/checks/SelectedCutRefinement.body.lean` | `14813200d24d78c3da98cdc7508400e3b82251cfed19f4dddbf4f81cfe190b18` |
| `work/checks/SelectedCutRefinement.prototype.lean` | `2ada5f1b4a38f717fef32c16c3007bd6caaff29b05cdb82af0aa500df3b1c140` |
| `work/checks/SelectedCutRefinement-first-kernel.log` | `284ebe316047c1c77f216bc7b7867be05e5fa14ab6fe1cb9641066df30b16ef6` |
| `work/checks/SelectedCutRefinement-prototype-result.json` | `bb8ab209bf192b3d41e45439d45b2da96f432ddb37fe19cb3474aebf768da8dc` |
| `work/lean/SM/NearFarFactorization.lean` | `5ba746897c43bb5382e4a409feba3c77acfca9bbbadcd6a5e708b94263d92628` |
| `work/lean/SM/RefinedChildren.lean` | `c201df125ee9221a73c9ce58a195fcec98e55c7c1b78de5616e1bdf94e5ea3d3` |
| `work/decisions/selected-cut-refinement-for-formal-cancellation-20260911.md` | `767619d67a6fdff3176310dc533d3cf91f015306921e1bf833d9f23f42fb5e53` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
