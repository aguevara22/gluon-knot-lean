# Incident flat gap tuples — technical review

2026-09-11. Independent technical review by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval** and not original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

## Findings

No mathematical defect was found in the seven frozen declarations, compared with the deletion-root definition in `sm-2-amplitude.tex` lines 380–386 and the incoming/outgoing cases of `thm:A-S3` at 435–452.

1. **Both full label words are proved.** `incoming_flat_gap_labels` and `outgoing_flat_gap_labels` quantify over every child label i and identify the sampled parent label with `deletionIndex j (i - 1)`. For incoming R, the global position is 1 plus the natural representative of i - 1; casting that sum and simplifying the root j - 1 gives exactly the deletion index. For outgoing L, the global position starts at zero and gives the same index. The modular representative is retained throughout, including i = 0; no unchecked natural-subtraction or wrap rule is used.
2. **Tuple equality is pointwise, not inferred from endpoints.** The two tuple theorems use function extensionality and apply P to those label identities. They conclude that each entire closed gap tuple is `shift (-1) (deleteVertex P j)`. The explicit child-label type and `erw` address definitional reduction at the existing size-indexed expressions. They do not alter the sampled tuple or replace a label equality by a weaker geometric equivalence.
3. **The fused root is correct.** The shift definition reads local label i as deletion label i - 1. Thus local root 0 has deletion endpoints -1 and 0, which `deletionIndex_last` and `deletionIndex_zero` identify with the ordered physical vertices j - 1 and j + 1. The integer theorems' root is literally `fusionIndex j (j - 1)` or `fusionIndex j j`; `fusionIndex_prev` and `fusionIndex_deleted` identify each with -1. Applying `treeCoefficient_shift` with both original root and shift equal to -1 makes the shifted root 0. This is the source fused edge with its orientation preserved.
4. **The congruence helper is legitimate dependent transport.** `treeCoefficient_congr_tuple` assumes equality of the actual tuples, substitutes that equality, and closes by reflexivity. The G1 proofs then have the same proposition as type and are identified by Lean proof irrelevance. It does not assume invariance under arbitrary equivalences, erase a geometric premise, or introduce an axiom. It is used before the independently proved cyclic-shift coefficient theorem.
5. **The integer B outputs are the source ones.** Both gaps have m + 2 leaves, so the leaf case is excluded even at m = 0. Unfolding `criticalIntervalIntegerOutput` leaves the actual restricted-word tree coefficient, with its previously proved G1 witness. The tuple congruence and shift theorem identify it with the actual deleted tuple's integer tree coefficient at the fused root. `g1_deleteVertex hz` derives deletion G1 from the sole zero turn support; parent G1 and strict betweenness are unnecessary for this tuple/coefficient identification. No inverse-coordinate integrality is asserted.
6. **Arity is handled explicitly.** Parent arity is m + 4 and both restricted/deleted tuple arities reduce to m + 3. This includes parent arity four and a triangular deletion. Every source arity N ≥ 4 admits m = N - 4 with N = m + 4, so the parameterization does not exclude a source size. The general-N wrapper and complete all-root flat-law assembly are nevertheless not among these seven declarations and remain pending.

The inspected dependency path is actual restricted/deleted label definitions → whole-tuple equality → proved coefficient congruence → cyclic covariance → nonleaf integer B. No flat-law equation is assumed. The earlier physical-root and gap-G1 reviews supply corroborating context; these seven declarations themselves do not finish the nonincident contraction, U/V simplification, or source side-order assembly.

## Receipt and repair verification

All **9/9** receipt hashes match current bytes. Every listed body occurs verbatim exactly once in the prototype. Root's **fourth session 40179** exited 0 and prints all seven declarations with only `propext`, `Classical.choice`, and `Quot.sound` (or subsets). The passing log contains no error, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`. No Lean kernel or build was run by this reviewer.

Sessions **69961**, **71741**, and **92571** are preserved failures, not passing evidence. Their logs document size-indexed simplification/rewrite mismatches, dependent-G1 rewrite motives, and then unresolved child-arity inference. Comparing declaration statements before `:= by` shows all original six statements are byte-for-byte unchanged in the first, second, third, and passing bodies. The third body adds the proved congruence helper, whose statement is also unchanged in the passing body. The final repair only specifies `(k := m + 3)` at its two call sites.

The receipt hash binds its full nine-file manifest. Principal SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/IncidentFlatGapTuples.body.lean` | `1b7035b83d8b6d8f91118233ecb3140bae49465bd715ba28a507077371106915` |
| `work/checks/IncidentFlatGapTuples.prototype.lean` | `1dc922d5182c56697c0be337cc08c1c0a4992788250e0beb0f1714d1fb51fbb8` |
| `work/checks/IncidentFlatGapTuples-fourth-kernel.log` | `025e223023fca986bcdd431a5672de8b23d573c4c3687465316e3beee159007c` |
| `work/checks/IncidentFlatGapTuples-prototype-result.json` | `44acdf402142ef984f162d55ac24d2d207968e42464848132f2f37c6bedcb674` |
| `work/lean/SM/RestrictedWordRoot.lean` | `a2d45634865602373437222b5e190794f31375624fa3021745ae6a0043551e8e` |
| `work/lean/SM/DeletionIndices.lean` | `15078436d16d1d233a3005ebdd5027156dd36200236a5a7928eef9e4071cec58` |
| `work/lean/SM/DeletedTuple.lean` | `b2e591d11b1f25d82511de7979be131fb2158e7bf3a62a0e3e962f1e2cca634c` |
| `work/lean/SM/FusionIndices.lean` | `6ea253ca0032b57388319e838d7aac9d985ad1144589261a6606ac32dc9f468f` |
| `work/lean/SM/DeletionG1.lean` | `84dc86e59d7baee28017ae1c01871769a90741aba59002869ccdb40cdc4881b7` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Hashes and recorded successful checks bind the inspected artifacts; they do not provide stronger fidelity approval. No frozen Lean body, canonical file, map, or acceptance status was edited.
