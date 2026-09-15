# Flat contraction arithmetic and arity transport — technical review

2026-09-11. Independent technical review by another agent of the **same currently available model**, **not stronger-model statement-fidelity approval** and not original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

Reviewed: five declarations in `FlatContractionArithmetic` and three in `TupleArityTransport`. No mathematical defect was found within their stated scope.

## Findings

1. **The erased count and child size are exact.** For the consecutive triple with positions k-1,k,k+1, `consecutive_erased_one` substitutes those actual endpoints into `upper - lower - 1`. The positive/interior bounds justify the natural subtraction and give exactly one erased position. `consecutive_contracted_size` therefore gives child size q for parent size q+1. These statements neither drop an endpoint nor confuse the two-edge span with two erased vertices. The arithmetic helpers allow smaller cases where meaningful; the source flat arity bound still gives q ≥ 3 when they are applied.
2. **The root calculation uses the existing physical deletion map.** `nonincident_fusionIndex_eq` starts from the actual boundary equation for j and excludes g=j using nonincidence. It computes the parent residue of `g - (j + 1)` as the natural number q-k-1, proves that representative lies below q+1, and then unfolds `fusionIndex`. The interior bounds also place q-k-1 in [0,q), so the final child cast is its true representative. At parent arity four, the possible k values 1 and 2 give the expected child root representatives 1 and 0. This does not replace the existing map by an abstract root choice.
3. **The cut relation is in the correct modulus.** `nonincident_fusionIndex_cut_relation` combines that child root with k+1 to obtain zero in `ZMod q`. Its natural subtractions have explicit lower bounds before casting, and the q term is reduced in the child modulus. This is the relation needed to compare the contracted reading with a cyclic shift of the deleted reading.
4. **Both modular representative cases are covered.** `zmod_cut_shift_val` puts v = `(u - 1).val`, uses v < q, and derives that u+a is v-k modulo q from the supplied cut relation. When v < k, the representative is v+q-k; when v ≥ k, it is v-k. Each branch proves the natural subtraction bounds and that the resulting representative is below q before applying `ZMod.val_natCast_of_lt`. The equality boundary v=k is in the second branch and yields zero. The first branch's last value v=k-1 yields q-1; k=0 is also covered by the second branch. Thus neither the wrap nor a boundary point is omitted. The general hypothesis k<q is exactly supplied by the nonincident interior bound.
5. **Size transport is equality induction.** `g1_reindex_size` and `treeCoefficient_reindex_size` use a proof n=q, substitute it, and split the definition of `ZMod` to reduce `ringEquivCongr` to the identity. The full tuple is precomposed by the inverse equality equivalence, while the actual root is sent by the forward equivalence. The tree coefficient, G1 witness and arity proof are transported together. This asserts no invariance under an arbitrary permutation or change of physical root.
6. **The tuple-comparison helper retains its substantive premise.** `treeCoefficient_of_reindexed_tuple_eq` additionally requires equality of the entire reindexed tuple with Q. After substituting the size equality, the proof reduces that premise to P=Q, substitutes Q, and uses reflexivity; proof irrelevance handles the two G1 witnesses. It does not infer tuple equality from endpoint agreement, G1, or matching arities. Its actual tuple-equality premise must still be proved in the nonincident application.

The source comparison is with the nonincident paragraph of `thm:A-S3`, `sm-2-amplitude.tex` lines 425–434, and the deletion-root definition at 380–386. Relevant definitions were inspected in the consecutive-boundary and contraction-position candidates, `FusionIndices`, `TreeCoefficient`, and mathlib's `ZMod.ringEquivCongr`. The eight declarations provide the arithmetic and dependent-type transport for the asserted one-vertex deletion. They do not yet prove the full nonincident tuple identification, signed amplitude response, or complete source flat law. No circular response assumption occurs.

## Receipt and hash verification

All **7/7** arithmetic receipt hashes and **3/3** transport receipt hashes match current bytes. Each listed body occurs verbatim exactly once in its prototype. Root's arithmetic **first session 93700** and transport **second session 29466** exited 0. Their logs print all five and three declarations respectively, with only `propext`, `Quot.sound`, and, for transport, `Classical.choice`. Neither passing log contains errors, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`. This reviewer ran no Lean kernel or build.

Transport first session **5271** is a preserved failure: it referred to an unavailable `RingEquiv.refl_symm` name and did not reduce the final equality-transport expression. Its log contains `sorryAx` for the third declaration and is not passing evidence. The successful repair splits n after substituting the size equality, extracts P=Q directly, clears the old dependent equality, and substitutes Q. All three declaration statements before `:= by` are byte-for-byte unchanged.

Receipt hashes bind the complete manifests, including dependency bodies. Principal SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/FlatContractionArithmetic.body.lean` | `45aa1ca887728c3d32dbf7a0e1df36966894d273d868bf6fc3a4f842eaa7f52a` |
| `work/checks/FlatContractionArithmetic.prototype.lean` | `bedfa416bb6bfd2f5d47d4805076ee00c9f3ef5af3dc59492e6e69e6d9999efe` |
| `work/checks/FlatContractionArithmetic-first-kernel.log` | `1fc2af33a61e482acd56ebdd80bcea0c39e2e65dfa95f10ea68324fb537160fa` |
| `work/checks/FlatContractionArithmetic-prototype-result.json` | `78a37164a253d09a5f87b40d72f3011d5a4bd2eeea431060308bbd12c1f556f9` |
| `work/checks/TupleArityTransport.body.lean` | `d18e9d42a019ba7a88be7963e0bb77ddaac1a32a2c533c77ddc779de7cbb002f` |
| `work/checks/TupleArityTransport.prototype.lean` | `e1ee69eba9a5c04f9c8d5d4d69b36cc87f642879877fac2bfa9a84e54ec66ce0` |
| `work/checks/TupleArityTransport-second-kernel.log` | `da0a2c45e5a575ed031391c74e7b21402d6078bd0c42763abdc6b9eb5797d0b4` |
| `work/checks/TupleArityTransport-prototype-result.json` | `2fd4b62633498fb6dce26650fd006ba354ded53f11f8b5aa7be4dc11c59886dc` |
| `work/lean/.lake/packages/mathlib/Mathlib/Data/ZMod/Basic.lean` | `844baab1b85ab66c4264402d69b7a8e75e55a1df62a340732cb880935410f6fd` |
| `work/lean/SM/FusionIndices.lean` | `6ea253ca0032b57388319e838d7aac9d985ad1144589261a6606ac32dc9f468f` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Recorded successful checks and hash agreement bind this technical review without establishing stronger fidelity approval. No frozen Lean body, canonical file, acceptance map, or status was edited.
