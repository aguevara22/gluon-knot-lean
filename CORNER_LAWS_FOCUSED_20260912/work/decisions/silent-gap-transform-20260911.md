# Actual silent gap transform: implementation note

Authored implementation by review_contraction_candidates, another agent of the same currently available model. Root owns independent review and every Lean/kernel/build run. This is not a self-review, stronger-model fidelity approval, or source acceptance. No kernel/build/audit was run and no frozen proof or map was edited.

New body/prototype: `work/checks/SilentGapTransform.body.lean` and `.prototype.lean`; exact first-draft copies are preserved. Five declarations:

1. `SM.intervalFarValue_left_mul`: scalar multiplication commutes with the actual fixed-endpoint conditional value, including outside its open interval.
2. `SM.silent_gap_intervalFarValue`: for any actual outer composition π whose rational geometric far entries all vanish, every interior cut j of any raw composition σ of actual gap k satisfies the outer-to-gap array identity in any CommRing R. Its epsilon is exactly `lineGapEpsilon (selectedLineCoordinate P g π.cut) k`.
3. `SM.silent_gap_intervalFarCutWeight`: for arbitrary η:R, the positional cut weight equals the negative half of `η * cast(epsilon) * geometricBoundaryArray(σ.farTriple j)`.
4. `SM.silent_gap_positionCutSummand`: the entire σ summand equals its actual nearFarWeight with zero near array and that scaled gap far array, times the original product of X at every actual child interval.
5. `SM.silent_gap_positionCutSum`: summing over every raw σ yields precisely `farTransform (fun t => η * cast(epsilon) * geometricBoundaryArray P g t) X (π.part k)`.

Proof steps: σ's far triple supplies strict bounds inside π.part k; canonical π.part_bounds supplies strict containment inside I. `silent_composition_cuts_collinear` derives actual determinant collinearity from the rational zero hypotheses. `weak_selected_gap_far_array_of_collinear` constructs the line coordinates and supplies the sign identity. The selected outer triple is identified entrywise with `(I.left, σ.interiorPosition j, I.right)` using π.first and π.last; the selected gap triple is identified entrywise with σ.farTriple j. Only then is intervalFarValue's interior branch unfolded. Scalar multiplication, the negative half factor and the full finite cut/child products are preserved exactly.

There is no new π.parts≥2, G1, full-root, child-genericity, nonzero further-cut, affine-coordinate or gap-identity premise. π.parts_pos supplies the selected endpoint condition even for a unary outer composition. Unary inner compositions have no cut indices, so the same product proof retains their sole actual child. One-leaf gaps and further zero factors remain in the complete sum. R is arbitrary CommRing for the value identity and has only the expected invertible-two premise for cut weights/transforms; η is unrestricted.

The prototype imports SM.Farout, SM.EuclideanPlane, SM.WeakGeometry, SM.NearFarFactorization, Mathlib.Data.Fintype.Lattice, and Mathlib.Tactic. It embeds the thirteen exact dependency bodies below, each once. At authorship, SilentCompositionLine has passed root second68161; TopFarDecomposition is in root first9281. If root repairs the latter, regenerate only this prototype embedding from the newly frozen dependency while preserving this draft. The new proof body is not claimed checked until root tests it.

This supplies the actual gap-transform factor in the top decomposition. The nonunary vanishing argument, formal-array constancy/inverse uniqueness and final full-root output theorem remain root's separate assembly work.

SHA-256 bindings:

| File | SHA-256 |
|---|---|
| `work/checks/SilentGapTransform.body.lean` | `cd5fa17cde20c28806f14f5c790a90da41cc1b1a1d599f0cf88d29fd410b4295` |
| `work/checks/SilentGapTransform.prototype.lean` | `3b36a7cb30e3af29747ef9ecd1c192f341eb579176b650609727c45e5915bb79` |
| `work/checks/SelectedCutRefinement.body.lean` | `14813200d24d78c3da98cdc7508400e3b82251cfed19f4dddbf4f81cfe190b18` |
| `work/checks/PositionalCutDecomposition.body.lean` | `ed59789e73793bd8b885ab65bd9096abe7065de2b7cd4386f19de6ff26a82b6d` |
| `work/checks/TopFarDecomposition.body.lean` | `2cc1eb1027a60fd62c29ba50c6e933c3ea3c84ec524b550fda66a3be4cdf4231` |
| `work/checks/CollinearGateSigns.body.lean` | `a26b36fbead365ba221a10ec0658fc5d7c6e70462e924f9c4e7d5d5c4cfd4e40` |
| `work/checks/InternalGapSigns.body.lean` | `09846a9e9beba9fdf6a68b7c7f32e1dfc7c46b3bd12fb3cdfee33d4d67355a6c` |
| `work/checks/WeakLineGeometry.body.lean` | `33fa407bf8a5c37dd2c9459d56e50cb3c48faa85f48076f679a2197694135dc3` |
| `work/checks/WeakLineSelections.body.lean` | `a91324f0380378fd48fcecea0bb1642f52dcdcc9fbfd45c626d43209cc6782c5` |
| `work/checks/FiniteLineGaps.body.lean` | `9d7d3e76bb2e142b2e675922d663fa116ab03ba6e3908fd8ec809e8b980ed2bd` |
| `work/checks/LineCoordinateNormalization.body.lean` | `95806b56f50651011b05d31989e3ce43076c9a129ac9a7de6f0f08d903c37797` |
| `work/checks/WeakSelectedLineCoordinates.body.lean` | `a711895a3661f741753269d46d480168b15840561b488d7a8ebd78c17b431d3b` |
| `work/checks/SilentLineGap.body.lean` | `466edcf63484a6e2f4d41a038164383d6d0e216c325c964ad41b27cfa433f5a7` |
| `work/checks/SelectedGapFarArray.body.lean` | `51a021cbde0a113355cf7657f9a94e331dac24721840692c31afc63c4eabd031` |
| `work/checks/SilentCompositionLine.body.lean` | `4d3e7ed775b33529bc1c55fa9695ab4c3dd8fa913ab5397aafddc8e431300da9` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Acceptance unchanged: 39/192 (20.3%); targets 0/8. Stronger fidelity remains separate.
