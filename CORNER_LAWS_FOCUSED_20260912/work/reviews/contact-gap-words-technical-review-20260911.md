# Concrete contact gap words — technical review

2026-09-11. Independent technical/source comparison by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval**, and supplies no original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

Root authored the four reviewed declarations in `ContactGapWords.body.lean`. This reviewer authored their `ContactBoundaryPositions` dependency, which root checked and reviewed separately as nonauthor; this report inspects its use without presenting an author's re-review as independent evidence. This reviewer ran no Lean kernel or build.

Compared all four statements and proofs with the nontrivial gap words in the `thm:A-S7` proof, `reference/SM/sm-2-amplitude.tex` lines 530–578, and the source halves in `sm-1-polygons.tex` lines 1230–1240. No mathematical, domain or definition defect was found.

Writing d for `contactDistance M a`, the results are exactly:

| Concrete gap | Proved number of vertices | Proved start | Complete reindexed tuple |
|---|---|---|---|
| base root, left gap | n-d = `secondHalfSize` | B | `secondHalf P M a` |
| base root, right gap | d+1 = `firstHalfSize` | X | `shift (-1) (firstHalf P M a)` |
| first inherited arc, right gap | n-d = `secondHalfSize` | B | `secondHalf P M a` |
| second inherited arc, left gap | d+1 = `firstHalfSize` | X | `shift (-1) (firstHalf P M a)` |

Each existential `hsize` is **constructed in the proof**, using the exact gap-count theorem and the definitions of the named half sizes. In the n-d cases, `contactDistance_bounds` ensures subtraction followed by adding 1 is justified. Starting labels are likewise obtained from the actual triple's label theorem. The caller supplies neither a size equality nor a starting-label oracle.

The tuple equalities use the generic `restrictedWord_eq_secondHalf` and `restrictedWord_eq_shift_firstHalf` theorems with those proved data. Their pointwise reindexing formula covers every residue, including zero; equality of endpoints alone is not used to identify the word. In the second-half cases local zero is X and local one is B, so the gap closure is the source opening edge X→B at half root 0. In the first-half cases local zero is A and local one is X; the shift makes local root 0 the source closing root -1 at A→X. All intermediate vertices are retained in the source cyclic order. The base gap order is λ₂ then λ₁, exactly as in the source; it does not exchange the named halves. Any later product reordering must use scalar commutativity explicitly.

The first inherited-arc hypothesis is only `(g-M).val < d`, and therefore includes the edge starting at M (offset zero) and the edge ending at A (offset d-1). The second is only `d < (g-M).val`, including the edge starting at B (offset d+1) and the edge ending at M (offset n-1). The previously proved root-partition equivalences identify these inequalities with the complete source arcs. No extra seam exclusion is present.

The domain is arbitrary actual tuple P, n nonzero, source bound `3 ≤ n`, and `ContactSeparated M a`, plus the appropriate root inequality for each inherited case. Contact separation implies the stronger actual size bound and both nonleaf gap lengths, rather than imposing a new caller condition. No wall-side choice, bigon/sliding restriction, G1 assumption on the center, flat premise, or affine coordinate is added. Geometry is unnecessary for these full word identities.

These four results remove the generic start/size premises for the actual source gaps. They do not identify the **contracted surviving** tuples in the proper-span branches, or prove the final S7 coefficient response; those remain separate work. No such equality or response is assumed here.

## Frozen evidence

All **7/7** receipt hashes match current bytes; each of the five listed bodies occurs verbatim exactly once in the prototype. Root's first session **49933** exited 0. All four printed declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; the log contains no `error:`, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`.

Principal SHA-256 bindings, relative to the focused root:

| File | SHA-256 |
|---|---|
| `work/checks/ContactGapWords.body.lean` | `27891ffab2f368aa0afe2ffb333d14b17dc50a2aa9aec7cc457abc4bad50087d` |
| `work/checks/ContactGapWords.prototype.lean` | `db6a09eb4bef91bc8b082e15ba3ca26ad2bdccae1f84b6ebda291449f2f066d0` |
| `work/checks/ContactGapWords-first-kernel.log` | `532c098a4784f7161cb6a13230b9b3da8a97a9237b6c47f064d38008fdb4d0e1` |
| `work/checks/ContactGapWords-prototype-result.json` | `8de2f991ccb57954130b9b4e634ef2d4cdbe42245a00a5edf6d0f3574b20e686` |
| `work/checks/ContactBoundaryPositions.body.lean` | `61d797a366cb8db5312ac0739037da47361b87eed4ed50e786ee3b72b7c2c4b7` |
| `work/checks/ContactGapTuples.body.lean` | `e10aa2e1663e8a0aa962b3606fcca260e53e73ef0c14077f09b59971e4f86945` |
| `work/checks/TupleArityTransport.body.lean` | `d18e9d42a019ba7a88be7963e0bb77ddaac1a32a2c533c77ddc779de7cbb002f` |
| `work/lean/SM/ContactHalfSizes.lean` | `801a5afe127b3640e922847d052696e88e2998c4e92bbc8af4b851291c1c1140` |
| `work/lean/SM/ContactHalfTuples.lean` | `10656209764059bc91a9a16cde47b3ec0b136a6d0112e5932a61bb841721a51f` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Hash agreement and successful checks identify the inspected artifacts without establishing statement fidelity. No reviewed proof, frozen evidence, canonical/source file, map or acceptance status was edited.
