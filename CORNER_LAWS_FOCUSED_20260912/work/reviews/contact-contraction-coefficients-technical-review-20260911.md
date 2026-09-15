# Contact contraction coefficients: technical review

2026-09-11. Reviewer: another agent of the same currently available model. This is independent technical/source comparison of the two root-authored declarations, **not the stronger-model statement-fidelity approval requested by the user**, and not source acceptance. No Lean/kernel/build was run; no frozen body, canonical file or acceptance map was changed. I authored the boundary-position and integer-factor dependencies; this review checks their application, not an independent re-review of those authored proofs.

**Finding:** no mathematical or domain defect found in `contactFirstArc_contracted_coefficient` or `contactSecondArc_contracted_coefficient` within this review's scope. They identify actual integer coefficients of the contracted tuples with the appropriate named halves at inherited physical roots. They do not yet assert the vertex-edge jump law.

The source comparison is to `sm-2-amplitude.tex`, induced half-root map at lines 386–394 and the two inherited-arc cases of `thm:A-S7` at lines 559–578, together with the named halves in `sm-1-polygons.tex`, Definition deletion-halves. The first half retains the arc from M to a; the second retains the arc from a+1 to M. Their ordered root labels are respectively `(g-M).val` and `(g-a).val`, cast into the relevant child arity.

The hypotheses are an arbitrary labelled tuple, `3 ≤ n`, `ContactSeparated M a`, the appropriate strict arc inequality, and the actual singleton point-zero support. No caller-supplied tuple identity, G1 witness, child arity bound, affine coordinate or root invariance is assumed. The child bounds follow from `contactHalfSizes_bounds`; the half G1 facts follow from the singleton support. The contracted G1 fact uses the proved exact cut support, not a new geometric premise.

Each proof first uses the corresponding complete `contact…Arc_contracted_tuple` identity, including every label and the explicit equality of arities. `treeCoefficient_of_reindexed_tuple_eq` transports by equality induction at root zero; it does not permit an arbitrary permutation. The target is a cyclic shift of the named half. The proved `treeCoefficient_shift` is then applied with both its root and shift equal to the stated inherited child root; subtraction gives root zero on the shifted tuple. This is the correct direction of covariance, with no assumption that coefficients are root independent.

The underlying whole-tuple identities were separately reviewed in `contact-contraction-labels-technical-review-20260911.md`. Their first-arc range includes `g=M` and `g=a-1`; their second-arc range includes `g=a+1` and `g=M-1`, including the edge whose endpoint wraps to label zero. The closing/opening contact edges are not substituted for these inherited roots. Proof-irrelevant G1 witnesses are transported only after actual tuple equality.

Receipt `ContactContractionCoefficients-prototype-result.json` records root session **23343**, first run, exit **0**. I recomputed all **21/21** manifest hashes without mismatch and checked that all 19 bound bodies occur exactly once in the prototype. The log prints both expected declarations, with only `propext`, `Classical.choice`, `Quot.sound` in each axiom trace; no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker occurs. This verifies the recorded evidence; kernel success and hashes alone do not establish source fidelity.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/ContactContractionCoefficients.body.lean` | `b205652841dfed1f37a9ddf77d8f41e2fe033ef221f4b8af945407670f06d328` |
| `work/checks/ContactContractionCoefficients.prototype.lean` | `d61fc4398083cf35877ff07269290a1f46a1385a8d6369d867df7f86731ec6a3` |
| `work/checks/ContactContractionCoefficients-first-kernel.log` | `15de3ad6e287b60ec0797d70d60529c463b1623896304392c67c52aedcf9acc9` |
| `work/checks/ContactContractionCoefficients-prototype-result.json` | `8123cfd7dd7835bf55e113072f7f84d7d34260af23dba8df32a9ba4946f741c1` |
| `work/checks/ContactContractionLabels.body.lean` | `1f64ec78ee9419379e3fa58af25ad9b53c3e5ccb02323e7a9ad18600d677019f` |
| `work/checks/TupleArityTransport.body.lean` | `d18e9d42a019ba7a88be7963e0bb77ddaac1a32a2c533c77ddc779de7cbb002f` |
| `work/checks/ContactBoundaryPositions.body.lean` | `61d797a366cb8db5312ac0739037da47361b87eed4ed50e786ee3b72b7c2c4b7` |
| `work/checks/ContactIntegerFactors.body.lean` | `406f96eee710116768518910df04615235b4ee4842106b1d4d847dfd3fcb27e7` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |

The receipt hash binds the remaining verified manifest entries. Stronger statement-fidelity approval remains pending. Acceptance remains **39/192 (20.3%)**, targets **0/8**.
