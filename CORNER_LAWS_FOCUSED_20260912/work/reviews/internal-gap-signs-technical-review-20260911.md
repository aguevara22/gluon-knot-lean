# Arbitrary internal-gap signs: technical review

Independent technical/source comparison by another agent of the **same currently available model**, not the author of InternalGapSigns. This is **not the stronger-model statement-fidelity approval requested by the user**, and no source claim is accepted. No Lean kernel/build/audit or frozen-file/map edit was performed.

Compared all six declarations with source `pf:gap-sign-identity`, `reference/SM/sm-2-amplitude.tex:887–902`, and read the actual pointFarSign, sign_rescale_nonzero, determinant, cyclic-area and affine-difference dependencies. No mathematical, orientation, or coefficient-domain defect was found.

- The far sign uses the exact reversed order: `det(r - endpoint_last)(endpoint_first - endpoint_last)`. Cyclic determinant invariance rewrites this as the endpoint difference times the determinant of the line direction with the transverse displacement. The factor is **last minus first**, with no missing minus sign.
- `det_line_base_translation` removes translation along the line by proving that the added parallel component has zero determinant. It does not assume a special origin or a shared internal endpoint. `affine_line_far_determinant` consequently applies to arbitrary outer endpoints x,z and arbitrary transverse point r.
- `affine_internal_gap_determinant` compares completely arbitrary internal coordinates a,b with outer coordinates x,z. The exact multiplier is `(b-a)/(z-x)`; only nonzero outer coordinate difference is needed at this determinant stage. No scalar order or geometric containment is silently imposed. Specialization to actual selected gaps must be proved separately from their real position bounds.
- `affine_internal_gap_sign` also requires `b≠a`, making the multiplier nonzero. From `D_gap = multiplier * D_outer`, involutivity of a nonzero real sign gives precisely `sign D_outer = epsilon * sign D_gap`. This holds for either orientation of either endpoint pair. The transverse determinant is never divided out or assumed nonzero, so further silent cuts and even a zero line direction remain covered by the algebraic identity.
- `affine_internal_gap_zero_iff` follows because epsilon is nonzero in SignType, so it preserves and reflects zero far signs. `affine_internal_gap_sign_cast` maps the actual SignType multiplication first into integers, then into any commutative ring via the proved multiplication-cast identities. All division is performed in the real coordinate ratio, not in the coefficient ring; there is no characteristic, invertibility-of-two, injective-cast or division-by-sign assumption.

These are general affine helper statements. Their use on geometricBoundaryArray requires the actual selected point representations and nonzero coordinate differences, which this group does not assume have already been established for a polygon. This does not itself prove coefficient extraction or formal cancellation.

Root first7424 exited0. All 4/4 receipt-bound hashes match; both embedded bodies occur exactly once in the prototype. All six requested traces contain only propext, Classical.choice and Quot.sound, with no error, sorryAx, native_decide or Lean.ofReduceBool marker. This is read-only verification of root's frozen evidence, not an independent kernel run or stronger fidelity approval.

SHA-256 bindings:

| File | SHA-256 |
|---|---|
| `work/checks/InternalGapSigns.body.lean` | `09846a9e9beba9fdf6a68b7c7f32e1dfc7c46b3bd12fb3cdfee33d4d67355a6c` |
| `work/checks/InternalGapSigns.prototype.lean` | `6ffc9f007586a52b0c3524d8ff8f6acc6b0d439eee8a94c4493ed0c901a68e7d` |
| `work/checks/InternalGapSigns-first-kernel.log` | `22bcc5f150b2c85eddde03f20f70888b971ac7b7ec3477b9eae39eaae9b46854` |
| `work/checks/InternalGapSigns-prototype-result.json` | `96cc021dd8ba368cb72cfca855bf43d5d1b35bb8e25517ea413989cd35cb8ea2` |
| `work/checks/CollinearGateSigns.body.lean` | `a26b36fbead365ba221a10ec0658fc5d7c6e70462e924f9c4e7d5d5c4cfd4e40` |
| `work/lean/SM/Chirotope.lean` | `e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575` |
| `work/lean/SM/Polygon.lean` | `d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Stronger statement/definition fidelity and source acceptance remain pending. Accepted progress remains 39/192 (20.3%); targets 0/8.
