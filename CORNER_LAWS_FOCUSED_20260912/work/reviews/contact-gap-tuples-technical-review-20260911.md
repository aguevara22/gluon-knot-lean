# Contact gap tuples — technical review

2026-09-11. Independent technical/source comparison by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval**, and supplies no original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8. Root authored the five reviewed declarations; this reviewer ran no Lean kernel or build.

Compared `ContactGapTuples.body.lean` with the complete closed gap words in the `thm:A-S7` proof, `reference/SM/sm-2-amplitude.tex` lines 530–578, and the source half definitions and roots. No mathematical or definition defect was found.

`restrictedWord_reindex_start` proves an identity at **every** label u of the size-reindexed tuple. It transports subtraction by 1 through the actual equality-of-sizes ring equivalence, using preservation of natural representatives. Expanding `globalPosition` then gives the parent label equal to the gap's starting label plus (u-1).val. The explicit `change` reduces the dependent Fin projection before the representative rewrite. This is not an endpoint-only argument or an assumption of invariance under arbitrary permutations.

`restrictedWord_eq_secondHalf` applies that universal identity to a gap starting at B = a+1 with `secondHalfSize` vertices. The canonical identity `secondHalfIndex_range` reads exactly the same parent labels, including u=0. Thus the entire reindexed tuple is λ₂ itself: local label 0 is X and label 1 is B. Its closed-gap root X→B is the source half's **opening** root 0.

`restrictedWord_eq_shift_firstHalf` applies the same identity to a gap starting at X = M with `firstHalfSize` vertices. The entire tuple is `shift (-1) (firstHalf P M a)`, not λ₁ with an incorrectly preserved zero root. Local label 0 is A and label 1 is X, so its closing root A→X is the source first-half root -1. All intermediate vertices follow from the universal identity as well. These orientations agree with d₁ and d₂ in `def:induced-roots`; no named half is exchanged.

The two coefficient theorems require the gap to have at least two leaves and supply explicit G1 proofs for both the restricted tuple and the relevant half. The gap bound and size equality imply that both coefficient arities are at least three; no formal leaf is passed off as a polygon amplitude. `treeCoefficient_of_reindexed_tuple_eq` transports the entire proved tuple, its G1 witness and root zero by equality induction. The first-half case then applies the proved cyclic shift formula with both source root and shift equal to -1, so the shifted root is zero. The second-half case needs no shift. Both equalities are between actual integer `treeCoefficient` values, with no division, inverse-coordinate integrality claim or root independence.

The tuple lemmas are geometric identities for arbitrary P and actual boundary interval J, conditional on the exact start label and size equality. The coefficient lemmas additionally retain their local G1 and nonleaf conditions. These are explicit helper premises, not hidden assumptions about the contact wall; concrete contact-cut specializations still need to prove them from the source data. This file does not establish the contracted surviving tuple, the final S7 coefficient product, or its sign. Within its stated scope it covers the source's two nontrivial gap words and closing roots without narrowing to bigon or sliding cases.

## Frozen evidence

All **4/4** receipt hashes match current bytes, and both listed bodies occur verbatim exactly once in the prototype. Root's first session **74248** exited 0. All five printed declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; the log has no `error:`, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`.

Principal SHA-256 bindings, relative to the focused root:

| File | SHA-256 |
|---|---|
| `work/checks/ContactGapTuples.body.lean` | `e10aa2e1663e8a0aa962b3606fcca260e53e73ef0c14077f09b59971e4f86945` |
| `work/checks/ContactGapTuples.prototype.lean` | `39afae55e21ca0f871e76c4ee05cb8f70ee808885a3edc3a7af81041e974ed64` |
| `work/checks/ContactGapTuples-first-kernel.log` | `011466ac29a5625662394cef7ba5baeaaa3fc838feaef70e3a7ba16d6043a20e` |
| `work/checks/ContactGapTuples-prototype-result.json` | `950b910e0a91d70b784700c2f3ff54094b4004006cf1bd1dba52eec9f83bb398` |
| `work/checks/TupleArityTransport.body.lean` | `d18e9d42a019ba7a88be7963e0bb77ddaac1a32a2c533c77ddc779de7cbb002f` |
| `work/lean/SM/RestrictedWordRoot.lean` | `a2d45634865602373437222b5e190794f31375624fa3021745ae6a0043551e8e` |
| `work/lean/SM/ContactHalfIndices.lean` | `137e1b2a30581d4ce11cee87a7b59c60b7cad24f039ee6a822f30559e2446323` |
| `work/lean/SM/ContactHalfTuples.lean` | `10656209764059bc91a9a16cde47b3ec0b136a6d0112e5932a61bb841721a51f` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Hash agreement and successful checks bind artifacts without establishing statement fidelity. No reviewed proof, frozen evidence, canonical/source file, map or acceptance status was edited.
