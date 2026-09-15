# Actual tree polynomial degree: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing root-authored `SupportedMultiaffine` (14 declarations), `CanonicalTripleDegree` (13), and `TreeTripleDegree` (6). This is **not the stronger-model statement-fidelity approval requested by the user**, nor source acceptance. No Lean/kernel/build, proof edit, canonical edit or acceptance-map change was performed. The reviewer authored `CompositionTripleSupports` and `PlaneTreeTripleSupports`; root's separate independent reviews are bound below. This report does not independently approve those self-authored dependencies.

**Finding:** no mathematical or domain defect found. The final theorem proves degree at most one in every independent canonical physical variable of the prescribed rational tree polynomial, with no geometric or disjointness premise supplied by the caller.

`SupportedMultiaffine p S` bounds `degreeOf x` by one on S and zero outside S. The canonical Mathlib definition is the maximum exponent of x among monomials with nonzero coefficient, so this is an actual unrestricted polynomial-ring statement. S is a permitted support bound, not an assertion that every member occurs. Zero and constant polynomials have degree zero, including the empty-support and empty-product cases. Addition and finite sums use maximum degree bounds; negation preserves degree; multiplication by a constant cannot increase it.

For `mul_disjoint`, degree of a product is bounded by the sum of the two individual degrees. Disjoint supports prevent both summands from being positive at the same variable. Outside their union both bounds are zero. The finite-product induction proves disjointness between each newly inserted support and the union of the remaining supports before applying that product bound. Its explicit pairwise premise concerns the polynomial family and is appropriate as an algebra helper; every such premise is later proved for the actual tree. No nonzero-polynomial premise excludes binary zero factors, and no cancellation or evaluation relation is needed.

`canonicalSupport` is the image under the proved injective map from boundary-position triples to source physical variable indices. Consequently it preserves disjointness, as well as the required union and finite-union identities. A formal boundary chi is one signed variable, so its support bound is its canonical singleton. The two terms of each actual cut factor are enlarged to the same two-triple support before addition/subtraction and multiplication by one half. Near/far coincidence at a binary cut therefore stays inside a single linear factor; it is not treated as multiplication of two independent variables. Distinct cut factors have disjoint supports by the proved composition theorem, and injective canonical transport retains that disjointness. Both ordinary and root composition weights receive the bound, including unary empty products.

The node-support disjointness theorems derive top-versus-child separation from actual cut positions and the entire child-tree support. They then extend it to the finite union of all children. `RootedPlaneTree.canonical_cut_nonrepetition` transports the actual occurrence theorem to physical canonical variables; it does not merely compare chi values at a tuple.

`tripleSupport_node` and `RootedPlaneTree.tripleSupport_eq` prove the exact decomposition of all actual occurrences into top cuts and ordinary-child occurrences in both directions. `combine_supported` proves pairwise sibling disjointness from actual child intervals and proves top-versus-children disjointness from those actual supports. Its polynomial support hypotheses are explicit intermediate inputs, but its disjointness hypotheses are derived, not passed in. In the ordinary-tree induction, the leaf weight is one; the node weight is minus its actual ordinary composition weight times all actual child weights. The composition result and induction hypotheses discharge every support input. The root theorem uses its actual half-sum weight and has no two-or-more-child restriction, preserving the unary root.

Finally, `canonicalTreePolynomial_multiaffine` rewrites the prescribed recursion as the finite sum of all actual rooted tree weights, then bounds the degree of that sum by the maximum degree of its terms. The conclusion quantifies every canonical variable, for arbitrary fixed g and n≥3. It has no realizability, G1, root-independence, R, caller disjointness or support-certificate premise. It uses the unrestricted `MvPolynomial` degree, with no variable relations imposed. Combined with the separately reviewed exact polynomial and G1 evaluation, this supplies the degree step of source `lem:multiaffine` (714–797); the final all-clause wrapper is reviewed separately.

Receipt verification: `SupportedMultiaffine` second root **75825**, exit **0**, **3/3** hashes; `CanonicalTripleDegree` first **88201**, exit **0**, **10/10**; `TreeTripleDegree` first **61050**, exit **0**, **11/11**. Each exact body occurs once in its prototype. All 33 successful traces use only `propext`, `Classical.choice`, `Quot.sound`; successful logs contain no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool`. The preserved support first run **29366** failed branch simplification before arithmetic. Its exact proof-only diff replaces limited `simp only` by `simp_all [Finset.mem_union]`; every definition and theorem type is retained. Failed evidence is not accepted as a successful trace.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/SupportedMultiaffine.body.lean` | `58075dcbd077a6e91a76d518a0cc215aaf3753a85250f0d91d99d26c5f7ce000` |
| `work/checks/SupportedMultiaffine.prototype.lean` | `7c27a8042c223e49346c1f03c7c9b65234a872e1db3780f13dc95f3d652ad0c8` |
| `work/checks/SupportedMultiaffine-second-kernel.log` | `d1db746fd964897588783404c8fb5b057316c9182ba79a214aeb81c5a0b846a3` |
| `work/checks/SupportedMultiaffine-prototype-result.json` | `4cf73732a5c010098ef67d8ef476afc1985618f7403da2af2068c245ae5e4497` |
| `work/checks/CanonicalTripleDegree.body.lean` | `36eb125b7d21dde177de854179fdb0247343dea48094289a613a0f61ef8e9b72` |
| `work/checks/CanonicalTripleDegree.prototype.lean` | `85b774954513c915cd469c0417cae0de749e2945c7cb2bfe35b74b5ca09be137` |
| `work/checks/CanonicalTripleDegree-first-kernel.log` | `93314f1a1b1b6f106cc5ddfaf79a7be9c4388c05f57be1c095e62d9e9d8b356c` |
| `work/checks/CanonicalTripleDegree-prototype-result.json` | `3ae0fbd5b3ff4fa4ef1d945120e803de41a207e44c378e93bdfaba157e744feb` |
| `work/checks/TreeTripleDegree.body.lean` | `2c28ac956ae4afc1c6120ca8e7a9c16fd4a2936d6dcb0d7924e0da701c8036ef` |
| `work/checks/TreeTripleDegree.prototype.lean` | `80b63c59d107d4d400279c50702de81bd37566c8939a7cc7845e1034efbc4996` |
| `work/checks/TreeTripleDegree-first-kernel.log` | `4589e4aea00665cfa1ff853573fec8ebb856541bdbe9d61cda8d37650379cb03` |
| `work/checks/TreeTripleDegree-prototype-result.json` | `1898c48dad1a9786d4ccb50ada21937315fdf7b6d8ea94b164a765504ee25c34` |
| `work/checks/SupportedMultiaffine-first-failed.body.lean` | `8ffaea5a4b551432ec25344cf807652ad8c1225b83b9255b5fe273ff9fc6d10e` |
| `work/checks/SupportedMultiaffine-first-failed.prototype.lean` | `de4208e7fd5f66ebc81a1ded6eaa2ae2e9511909f939cd45fb3ee946bb7399fa` |
| `work/checks/SupportedMultiaffine-first-kernel.log` | `4e3904641dc1d2f9a883a6eecd9f7217e721cd3654386e8e980c82a53869c75b` |
| `work/checks/FormalOrderedChi.body.lean` | `1df0e2ad12df3d28dc32318201fe2a786eb880fe56ea2fff374f7fc3f2d3ebe6` |
| `work/checks/FormalTriplePolynomial.body.lean` | `138f5620027a3be64bbaed123b2a8ef6723b50fe6911bd4b2f6cf06a8b6c2d84` |
| `work/checks/PlaneTreeTripleSupports.body.lean` | `d21ef16f9f91c4ec13e1642badf233620c8f761e6b5c398f22b7aa7cea224b82` |
| `work/checks/CompositionTripleSupports.body.lean` | `c6600e67a028ccffb28c0aae1d02e782b689f24e823ddd3a49b297e0cb069cff` |
| `work/lean/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Degrees.lean` | `11fd527aebb2082f5e8770a295883d327cc3ea24b94b8823ed4e2bf1b5030f3f` |
| `work/lean/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/CommRing.lean` | `1bcf000a1a810cef37d48a43f1052a90f783e436967eafce362233c05cbad136` |
| `work/reviews/plane-tree-triple-supports-technical-review-20260911.md` | `781e35c5421159ec5aeec8c63d407b436096f0eee92c83f4a0034ab9b719a127` |
| `work/reviews/composition-triple-supports-technical-review-20260911.md` | `1873942067abdb990d28a5cd1b646ef0cf43d3379508a4201e08dd8a5d5e9355` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

The receipts bind remaining embedded dependencies. Hashes and passing proofs do not establish stronger statement fidelity. Acceptance remains **39/192 (20.3%)**, targets **0/8**.
