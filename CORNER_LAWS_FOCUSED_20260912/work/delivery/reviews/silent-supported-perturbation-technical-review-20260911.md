# Supported silent perturbations: technical review

Independent technical/source comparison of root-authored SilentSupportedPerturbation by another agent of the **same currently available model**. This is **not the stronger-model statement-fidelity approval requested by the user**. I authored the earlier FiniteLineGaps, SelectedCutRefinement, original PositionalCutDecomposition and SilentGapTransform helpers; root's separate nonauthor reviews are bound below. This report reviews the new assembly, not those authored mathematical constructions. No kernel/build/audit or frozen-file/map edit was performed.

Compared all five complete statements/proofs with source `pf:formal-cancellation`, `reference/SM/sm-2-amplitude.tex:845–936`, including simultaneous silent positions, zero gap factors, inverse uniqueness and the full-root restriction. No mathematical defect or unproved public gap premise was found.

`silent_scaled_top_eq` exposes a conditional eta-gap helper, then discharges the earlier every-nonunary-contribution hypothesis by an exhaustive split on the actual selected cuts of each outer composition:

- If every selected top cut is rationally silent, hgap supplies an actual gap k with at least two leaves and eta times its source epsilon equal to one. The proved actual gap-sum identity rewrites its entire inner sum to the scaled geometric far transform, with the **same** fixed inverse-coordinate array of the geometric base. The multiplier equation turns the far array into the base geometric array; canonical farOnly_nonleaf_E then makes that gap factor zero. A product containing this actual indexed factor vanishes. There is no nonzero assumption on other factors and no division or cancellation through a zero divisor.
- Otherwise an actual interior index j has nonzero rational geometric far value. The support hypothesis forces U at that exact far triple to zero. intervalFarValue_interior identifies the selected physical-position factor; eta times that U value and its negative half are zero. interiorPosition_mem proves this factor occurs in the selected physical Finset product, so that product vanishes. No selected cut is inferred merely from an interval endpoint or abstract membership certificate.

Thus every nonunary contribution is proved zero while the exact unary term survives. This is a complete finite polynomial decomposition argument. It bypasses explicit monomial-coefficient extraction without assuming the desired coefficient identity or restricting simultaneous formal assignments.

The four public consumers remove the conditional gap premise:

- `silent_supported_forward_top` uses the actual positive-gap lemma at eta=1 for every interval. Rational zeros give the selected line; WeakGeneric and source n≥3 give a nonleaf epsilon=+1 gap.
- `silent_supported_reversed_full_top` uses the actual negative-gap lemma at eta=-1 **only on fullBoundaryInterval**. The two minus signs multiply to one in the coefficient ring. The physical root endpoint requirements were proved in that gap lemma; no reversed-output claim is made for a general open interval.
- `silent_supported_coordinates` turns the proved forward equations at all intervals into one full array equation. Canonical nearFar_solution_unique for the actual triangular transform then identifies the entire inverse array. It does not assume a coordinate induction hypothesis or constancy of the perturbed inverse.
- `silent_supported_output` first rewrites the complete perturbed inverse array using that equality, then applies the full-root reversed top identity. The order of these steps avoids silently fixing perturbed child coordinates before they have been proved equal.

The public domain is any CommRing with invertible two, every WeakGeneric polygon of source size n≥3, every root and every simultaneous array U vanishing at all **rational** nonzero geometric entries. Rational zero support is essential for geometric zero reflection; no invalid arbitrary-ring cast reflection is used. U is otherwise unrestricted and need not be realizable. Zero divisors and other silent cuts are retained. A later polynomial wrapper must instantiate this generic result with the exact independent-variable array and identify the constant inclusion; that setup is not assumed here.

Root first11561 exited0. All 18/18 receipt-bound hashes match; all sixteen bodies occur exactly once. All five traces contain only propext, Classical.choice and Quot.sound, with no error, sorryAx, native_decide or Lean.ofReduceBool marker. This is inspection of root's frozen evidence, not an additional kernel run.

SHA-256 bindings:

| File | SHA-256 |
|---|---|
| `work/checks/SilentSupportedPerturbation.body.lean` | `fd4b2656d0073ce518f0460d28bace8528c87723b40682d533fb3f539b6c20ba` |
| `work/checks/SilentSupportedPerturbation.prototype.lean` | `2ccfcee01daf5a0e31cde72aa799b7e124597c8a38b175cfb855961e27967518` |
| `work/checks/SilentSupportedPerturbation-first-kernel.log` | `e4a479c7fbd233097af0e25300ea27cda1eb2001f53ac604f0e96c547b1a0801` |
| `work/checks/SilentSupportedPerturbation-prototype-result.json` | `c45c03daf6aca75461985c63d0c9357129c30e4463029e509969309151785d87` |
| `work/checks/TopFarCancellation.body.lean` | `fd57112cda0a7cfbfb7f15d91d224723e60f5ae5a7f9032f585aeeccae882a44` |
| `work/checks/SilentCompositionLine.body.lean` | `4d3e7ed775b33529bc1c55fa9695ab4c3dd8fa913ab5397aafddc8e431300da9` |
| `work/checks/SilentGapTransform.body.lean` | `cd5fa17cde20c28806f14f5c790a90da41cc1b1a1d599f0cf88d29fd410b4295` |
| `work/lean/SM/FarOnlyOutput.lean` | `d773b636e2dc37babf11ae3df6b1eb813f5bc2812ad10f5e9bb76faf7d133aa4` |
| `work/lean/SM/NearFarTriangular.lean` | `851c9d30affbb3d38893bdc72249173f4b830d552768ba04e971e1ee848663b2` |
| `work/lean/SM/TriangularInverse.lean` | `c1ad3aab34d9695ee82fa41284461d921125d0d67281c1a67d46cbb48c0f5db2` |
| `work/reviews/finite-line-gaps-technical-review-20260911.md` | `e9c3e5eac643bbd0a9554a6ce386d57b1f89d84e30c3b4b41dd50546079fae23` |
| `work/reviews/selected-cut-refinement-technical-review-20260911.md` | `fdc5706133aabcdd77ca0c7419269866b257b8c77377f9cc2336904738af1c13` |
| `work/reviews/positional-cut-decomposition-core-review-20260912.md` | `5fd3bb4bf8bdff142159fbe4e01d0b81485e85efe886f5cc9447c13af94301e0` |
| `work/reviews/silent-gap-transform-technical-review-20260912.md` | `27442075ebc86ed020cf224d9be7f94f654cae1763db90fb33fdef1498a00ae0` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Stronger statement/definition fidelity and source acceptance remain pending. Accepted progress is unchanged: 39/192 (20.3%); targets 0/8.
