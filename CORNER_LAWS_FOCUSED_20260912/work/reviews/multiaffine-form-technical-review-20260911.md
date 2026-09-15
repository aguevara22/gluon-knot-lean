# Full multi-affine form: technical and source comparison

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing the root-authored aggregate `SM.multiaffine_form` against all of source `lem:multiaffine` (714–797). This is **not the stronger-model statement-fidelity approval requested by the user**, nor source-claim acceptance. No Lean/kernel/build, proof edit, canonical edit or acceptance-map change was performed. This reviewer authored `CompositionTripleSupports`, `PlaneTreeTripleSupports` and `PlaneTreeInternalIntervals`; root's separate independent technical reviews of those dependencies are bound below. This report reviews their use in the aggregate and does not represent an independent review of its author's own proofs.

**Finding:** no mathematical or domain defect, circular premise or missing advertised clause was identified in this limited same-model comparison. The seven conjuncts expose the prescribed unrestricted polynomial and every structural assertion printed in the lemma, including the binary and shared-interval qualifications.

1. The polynomial is the already defined `canonicalTreePolynomial g hn`, not an existential surrogate. Its finite signed-tree identity uses all actual `RootedPlaneTree` objects on the full boundary interval, one minus sign per ordinary internal node, the prescribed root half-sum weight, and all ordinary half-difference weights. The variable type consists of increasing triples in canonical physical label order: the preceding proved maps identify positions 0,…,n−1 with source labels 1,…,n, with source label n represented by residue zero. Ordered entries are interpreted as exact signed variables in the unrestricted rational `MvPolynomial` ring.

2. Every individual variable has `degreeOf ≤ 1`. This is the maximum monomial exponent in that actual polynomial, not a degree after evaluating realizable chirotopes or imposing relations. The reviewed degree proof derives support separation from the actual composition/tree data and adds no geometry or caller-disjointness premise.

3. Evaluation at the actual canonical chirotope values equals the rational cast of the original integer `treeCoefficient`, at the same root, for **every G1 tuple**. G2 is not required. The preceding factor evaluations derive their nonzero gate arguments from G1 and strict cut positions. This conjunct does not assign a value to a literal gate at zero or claim a silent-locus tree-sum evaluation.

4. A canonical physical variable belonging to the supports of two actual node-and-cut occurrences forces those occurrences to be equal. The occurrence type records each path of child choices and the actual cut index, so this is tree-level factor nonrepetition. It is not merely interval equality or distinctness of evaluated chi values. It permits the near and far entries of one binary factor to coincide, exactly as the source does.

5. For every binary composition, the aggregate explicitly gives equality of its formal near and far entries, zero ordinary factor, and root factor equal to the single entry. Equality is established in the formal ring from equality of the actual triples. Binary nodes remain in the tree family; their zero ordinary factor annihilates the corresponding vertex weight, and hence any signed tree product containing it. No binary-free restriction is used for the degree conclusion.

6. For distinct actual internal-node occurrences with equal leaf intervals, the root has exactly one child, and the two occurrences are the distinguished root and its immediate child in either order. `InternalOccurrence` includes the root even when it has no factors; `rootOccurrence` and `IsImmediateChild` are defined by the actual structural constructors, not by interval equality. The latter selects the top internal node of the chosen ordinary child, and parts=1 makes that child the sole one. Leaves are not misclassified as internal vertices. The separately reviewed interval proof establishes strict descendant decrease and sibling impossibility, rather than assuming this conclusion.

7. A unary root's formal root weight is one. It is the product over its genuinely empty cut-index domain, so the possible shared interval in the preceding conjunct introduces no extra factor or repeated variable.

The aggregate assumes only the source size n≥3 and a fixed arbitrary physical root (with `NeZero n` redundant under that bound). Its structural conjuncts quantify all actual intervals, compositions and trees, thus covering the full-tree instances without narrowing them. The proof directly assembles the preceding proved identities and geometric-free combinatorial/algebraic results; none of the conclusions is a caller premise. No root-independence, R identity, positivity, generic-path or support certificate is assumed. The next source line-gap lemma is outside this reviewed unit.

Verified receipt: first root **20791**, exit **0**, all **13/13** hashes match. The aggregate body occurs exactly once in its prototype. Its successful trace lists only `propext`, `Classical.choice`, `Quot.sound`; its log contains no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool`. The separate reviewed degree groups and earlier polynomial evidence are bound through their reports and the exact dependency bodies below. Passing proofs and hashes do not establish stronger statement/definition fidelity or controlled canonical integration.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/BoundaryTripleSupports.body.lean` | `60199670494951bea511f187f7f894fd63fd4d074237e5b0442602e2c4f02e42` |
| `work/checks/CanonicalTripleSigns.body.lean` | `76321d75b54c5a31611575577ecbf36bb1edaeef2142f0177bfd22f042fbbe54` |
| `work/checks/FormalOrderedChi.body.lean` | `1df0e2ad12df3d28dc32318201fe2a786eb880fe56ea2fff374f7fc3f2d3ebe6` |
| `work/checks/CompositionTripleSupports.body.lean` | `c6600e67a028ccffb28c0aae1d02e782b689f24e823ddd3a49b297e0cb069cff` |
| `work/checks/FormalTriplePolynomial.body.lean` | `138f5620027a3be64bbaed123b2a8ef6723b50fe6911bd4b2f6cf06a8b6c2d84` |
| `work/checks/PlaneTreeTripleSupports.body.lean` | `d21ef16f9f91c4ec13e1642badf233620c8f761e6b5c398f22b7aa7cea224b82` |
| `work/checks/SupportedMultiaffine.body.lean` | `58075dcbd077a6e91a76d518a0cc215aaf3753a85250f0d91d99d26c5f7ce000` |
| `work/checks/CanonicalTripleDegree.body.lean` | `36eb125b7d21dde177de854179fdb0247343dea48094289a613a0f61ef8e9b72` |
| `work/checks/TreeTripleDegree.body.lean` | `2c28ac956ae4afc1c6120ca8e7a9c16fd4a2936d6dcb0d7924e0da701c8036ef` |
| `work/checks/PlaneTreeInternalIntervals.body.lean` | `d517acbe05348e7f6c80d244e0150e32209e0ee7e9f2326c4799e2beff8d6b63` |
| `work/checks/MultiaffineForm.body.lean` | `4ea7a8b3e700da9113c6ea0add1ae170de308ecf4d84d2948f7a5da993ddcb78` |
| `work/checks/MultiaffineForm.prototype.lean` | `a213deb2aca069c9380ba2dab3dc8c66551ad8659e07134fb19f7e26c8c8a7d8` |
| `work/checks/MultiaffineForm-first-kernel.log` | `463700d75cba38b09dd38d32236f5e79a5586d1c1183583397f42a188c23588f` |
| `work/checks/MultiaffineForm-prototype-result.json` | `5e823e85e2105d05c82ee6ca3530a705fa5b5188283f2d24fa136391173d83e6` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `work/reviews/canonical-triple-signs-technical-review-20260911.md` | `42cc793b68b6117c3a0f322720b948e0c058bc6035dabc0ebb7ac8014826c040` |
| `work/reviews/formal-ordered-chi-and-tree-polynomial-technical-review-20260911.md` | `466b1f310c4e1ea91d653acbe0a211d93d37aabeaaccb3d3673e0d79388367f9` |
| `work/reviews/tree-multiaffine-degree-technical-review-20260911.md` | `797b4bdac5cf3cc52952d91d65d51d168b9a6ff26b0ecb6115a7a7b833d04846` |
| `work/reviews/composition-triple-supports-technical-review-20260911.md` | `1873942067abdb990d28a5cd1b646ef0cf43d3379508a4201e08dd8a5d5e9355` |
| `work/reviews/plane-tree-triple-supports-technical-review-20260911.md` | `781e35c5421159ec5aeec8c63d407b436096f0eee92c83f4a0034ab9b719a127` |
| `work/reviews/plane-tree-internal-intervals-technical-review-20260911.md` | `dc180cc255b5b32f91cb760efb7f0b27a77ea9279c91deda877d5c6935a0c8f7` |

Stronger fidelity review and the acceptance/integration process remain pending. Acceptance remains **39/192 (20.3%)**, targets **0/8**.
