# Line normalization and constructed coordinates: technical review

Independent technical/source comparison by another agent of the **same currently available model**, not the author of these twelve declarations. This is **not the stronger-model statement-fidelity approval requested by the user**. No source acceptance, Lean kernel/build, or frozen-file/map edit was performed.

Compared LineCoordinateNormalization (two definitions/eight theorems) and WeakSelectedLineCoordinates (one definition/one theorem) with the exact ratio and coordinate choice in `reference/SM/sm-2-amplitude.tex:795–842`. No mathematical, sign, or domain defect was found.

1. `lineGapEpsilon` uses the source's numerator (next coordinate minus previous coordinate) divided by the **last-minus-first** endpoint difference. Lean gap index `j:Fin k` represents printed gap `j+1`. `normalizedLineCoordinate` subtracts the first value and divides by the same difference. Injectivity and `0<k` prove this denominator nonzero from distinct actual endpoint indices; it is not supplied as a geometric assumption in the eventual source application.
2. The normalized first and last coordinates are zero and one. Injectivity is preserved by cancellation with a nonzero real denominator. No theorem assumes its positivity. The pointwise affine representation changes the origin to `p+t_0•ω` and the direction to `(t_last-t_0)•ω`; cancellation reconstructs every original point even when this scalar is negative. Thus normalization does not silently reverse or restrict the source's oriented ratio.
3. The difference of successive normalized coordinates equals the original gap ratio by distributivity over division. Positive/negative epsilon equivalences therefore compare exactly those normalized coordinates, using the actual `SignType.sign` tests. These algebraic identities also hold when a denominator is zero; the later nonzero proof is what licenses endpoint normalization and a genuine line coordinate.
4. `selectedLineCoordinate` is the actual dot product of the endpoint direction with the selected displacement, divided by its squared Euclidean length. With WeakGeneric, strict selected-index order and `0<k`, equality of endpoint points would contradict boundary-word injectivity and the distinct endpoint indices. The direction is therefore nonzero, and canonical `planeDot_self_pos` supplies a positive denominator.
5. The supplied collinearity condition is a zero **actual determinant** for each selected displacement and the actual endpoint direction. Swapping determinant arguments changes its sign, still zero; canonical `scalar_of_det_zero` then proves each exact affine point equation with the defined dot-product coefficient. This is not an existential coordinate oracle. The coordinate injection follows from the point equations and actual boundary-word/index injectivity; direct computation gives endpoint coordinates zero and one. Endpoint determinant conditions themselves are automatic zero equations and add no substantive restriction.

Neither group adds G1, a preferred line orientation, a fixed root, an `n≥4` assumption, or a condition forbidding other collinearities. The actual-coordinate theorem retains its determinant-collinearity premise because it formalizes the selected line. It supplies the affine data needed by the later source theorem; by itself it does not assert a nonleaf gap.

Root's first63737 and first74872 runs exited0. I verified all 3/3 and 5/5 receipt-bound hashes, exact body embeddings, and all ten/two log traces. Only standard foundations (`propext`, `Classical.choice`, `Quot.sound`) appear; no error, sorryAx, native_decide, or Lean.ofReduceBool marker occurs. Read the imported concrete definitions/proofs of planeDot, planeDot_self_pos and scalar_of_det_zero, as well as the selected geometry dependencies reviewed separately. Successful receipts do not establish stronger fidelity approval.

SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/LineCoordinateNormalization.body.lean` | `95806b56f50651011b05d31989e3ce43076c9a129ac9a7de6f0f08d903c37797` |
| `work/checks/LineCoordinateNormalization.prototype.lean` | `4cea19608a500066f298331772c49cf66c1fa6b37fa7b2d08faee6c87d8e6860` |
| `work/checks/LineCoordinateNormalization-first-kernel.log` | `8a7bb2e050fbacc823164129fa018a452b9df59ac7db42e331187d95f44448a7` |
| `work/checks/LineCoordinateNormalization-prototype-result.json` | `58224a8ede6a058b4f8cfbe50f6041f2ec4c1ea21babaebb48d0db87f0a425b1` |
| `work/checks/WeakSelectedLineCoordinates.body.lean` | `a711895a3661f741753269d46d480168b15840561b488d7a8ebd78c17b431d3b` |
| `work/checks/WeakSelectedLineCoordinates.prototype.lean` | `f3807d62c3eb6da90e7344a6ff274fd3d74817523b9732b0fffcb084d1405d2c` |
| `work/checks/WeakSelectedLineCoordinates-first-kernel.log` | `367ce743fae74128623fe342640e6722aa7daa12e78c356a9e8e6990d7103c31` |
| `work/checks/WeakSelectedLineCoordinates-prototype-result.json` | `d2c70a346a279af4453c887668b15340bdfb23429990d9d4bdd2c3f2ca5336a6` |
| `work/checks/WeakLineGeometry.body.lean` | `33fa407bf8a5c37dd2c9459d56e50cb3c48faa85f48076f679a2197694135dc3` |
| `work/checks/WeakLineSelections.body.lean` | `a91324f0380378fd48fcecea0bb1642f52dcdcc9fbfd45c626d43209cc6782c5` |
| `work/lean/SM/EuclideanPlane.lean` | `30a5956221225bc9811a792b5a67c6c5967fb6dda0b4cb14be997051b32b7a4f` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `work/reviews/weak-line-geometry-and-selections-technical-review-20260911.md` | `37b0b80802924ba2d39f71b68b1870114f05424764734f18302fec95e5ccf64a` |

Stronger statement/definition fidelity and source acceptance remain pending. Accepted progress is unchanged: 39/192 (20.3%); targets 0/8.
