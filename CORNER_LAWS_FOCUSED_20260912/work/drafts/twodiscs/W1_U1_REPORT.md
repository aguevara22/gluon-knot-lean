# Row 57 — unit U1 (convex/affine toolkit) — REPORT

Written 2026-09-19 by the U1 prover agent.  File: `work/drafts/twodiscs/W1_U1.lean`
(= `Skeleton_FINAL.lean` with the 21 `U1_*` leaves closed and `u1h_`-prefixed helpers inserted
immediately before the first leaf that uses them; 1 493 lines).

## 1. Result

* **All 21 U1 leaves closed** (SKELETON_REPORT §2 lines 269-373): `U1_triangle_isCompact`,
  `U1_triangle_convex`, `U1_triangle_interior_nonempty`, `U1_triangle_isDisc`, `U1_square_isDisc`,
  `U1_mem_carrier_iff_det`, `U1_frontier_triangle`, `U1_interior_convex_isConnected`,
  `U1_compl_compact_convex_isConnected`, `U1_affineOn_comp`, `U1_affineOn_mono`,
  `U1_isPositiveAffineOn_mono`, `U1_isPositiveAffineOn_comp`, `U1_exists_affine_of_triangle`,
  `U1_isPositiveAffineOn_of_det`, `U1_continuousOn_iUnion_of_finite`, `U1_isHomeoOnto_comp`,
  `U1_isHomeoOnto_inv`, `U1_isHomeoOnto_restrict`, `U1_isHomeoOnto_of_homeomorph`, `U1_isHomeoOnto_coe`.
* **No leaf statement changed, none found false** (rule 3 not triggered); no new intermediate from another
  unit was needed (rule 2 not triggered); nothing consumed from other units.
* Checks (all run on the final file, 2026-09-19):
  * `cd work/lean && lake env lean ../drafts/twodiscs/W1_U1.lean`: **0 errors**, 71 `declaration uses sorry`
    warnings, all at lines ≥ 831 (the U2-U11 leaves); none in the U1 block.
  * `python3 work/drafts/twodiscs/check_57_identity.py work/drafts/twodiscs/W1_U1.lean`: `IDENTITY OK` (DEFS, BUNDLE, THM).
  * `grep -c sorry`: **95 before → 74 after** (21 removed; the remaining 74 = 71 other-unit leaves + 3 docstring
    mentions of the word, exactly as in the skeleton).
  * `#print axioms` on a scratch copy for each of the 21 closed leaves: every one depends on exactly
    `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
* **Imports added** (allowed, not part of the identity check): `Mathlib.Analysis.Normed.Module.Connected`
  (`isPreconnected_sphere`), `Mathlib.Analysis.LocallyConvex.Separation` (`geometric_hahn_banach_closed_point`),
  `Mathlib.LinearAlgebra.Dimension.StrongRankCondition` (`Module.rank_self`).  Downstream unit files that start
  from `W1_U1.lean` inherit them; a file starting from the skeleton needs them only if it re-proves U1.

## 2. Routes taken (per leaf group)

* **Triangle basics.** `carrier = convexHull ℝ (range v)`: compact by `Set.Finite.isCompact_convexHull`, convex by
  `convex_convexHull`.  Membership by det signs (`u1h_mem_carrier_iff_det`, the body of `U1_mem_carrier_iff_det`):
  "⇒" by `convexHull_min` against the intersection of three closed half-planes (`u1h_convex_det_nonneg`, each
  convex by `nlinarith`), the vertices checked by `fin_cases`; "⇐" by barycentric coordinates
  `u1h_baryA T x = det (x - v0) (v2 - v0) / D`, `u1h_baryB T x = det (v1 - v0) (x - v0) / D` (Cramer,
  `u1h_bary_eq`), the three dets being `D * b`, `D * (1 - a - b)`, `D * a` (`u1h_det0/1/2`), then
  `Convex.sum_mem` with weights `![1 - a - b, a, b]`.
* **Interior and frontier.** `u1h_interior_triangle`: `interior carrier` = the open triangle.  "⊇" by
  `interior_maximal` (open: `isOpen_lt`); "⊆" by the perturbation lemma `u1h_interior_subset_pos` (if a set lies in a
  closed half-plane, its interior lies in the open one: move from a boundary point along the inward-negative
  direction `(u.2, -u.1)`, use `Tendsto.eventually` on `𝓝[>] 0`).  Edge vectors nonzero from `T.pos`
  (`u1h_edge01_ne` etc.).  `U1_triangle_interior_nonempty`: the barycentre `(1/3) • (v0 + v1 + v2)` has the three
  dets `= D/3 > 0`.  `U1_frontier_triangle`: `IsClosed.frontier_eq` + the interior formula, then each
  "one det zero, the others ≥ 0" set is the corresponding closed edge (`u1h_seg0/1/2` via barycentric coordinates;
  converse `u1h_det_segment` + `segment_subset_convexHull`).
* **Discs.** `U1_triangle_isDisc` = ⟨convex, compact, interior nonempty⟩.  `U1_square_isDisc`: `square L` is
  literally `Metric.closedBall 0 L` in the product (sup) metric of `Plane = ℝ × ℝ` (`Prod.norm_def`), so
  `Link.isDisc_closedBall` applies.
* **Connectedness.** `U1_interior_convex_isConnected`: `Convex.interior` + `Convex.isPreconnected`.
  `U1_compl_compact_convex_isConnected`: `isPreconnected_of_forall` from the far point `x₀ = (R + 1, 0)` (with
  `S ⊆ closedBall 0 R`): for `y ∉ S` take the Hahn–Banach functional `f` separating `y` from `S`
  (`geometric_hahn_banach_closed_point`), the direction `d = y - a` (`a ∈ S`, so `f d > 0`), and the connected set
  ray(y, d) ∪ {‖z‖ > R}: the ray misses `S` (`f` only grows), the exterior `{‖z‖ > R}` is preconnected as the image
  of `sphere 0 1 ×ˢ Ioi R` under `(u, r) ↦ r • u` (`isPreconnected_sphere`, rank of `ℝ × ℝ` is 2), and the ray
  meets it at `t = (R + ‖y‖ + 1)/‖d‖`.  Empty `S`: complement `univ`, `convex_univ.isPreconnected`.
* **Affine algebra.** `U1_affineOn_comp/mono`: compose the linear parts.  `u1h_det_linear`: `det (M u) (M v) =
  det (M (1,0)) (M (0,1)) * det u v`; with `u1h_affineOn_sub` this gives `U1_isPositiveAffineOn_mono` (the
  determinant of the linear part is positive because `T` is, then `T'.pos`).  `U1_isPositiveAffineOn_comp`: the image
  of the carrier is the carrier of `T.map f hf` (`u1h_affineOn_image_convexHull` via the bundled
  `u1h_affineMap M b = vaddConst b ∘ M` and `AffineMap.image_convexHull`); positivity is `hg.2` verbatim.
  `U1_exists_affine_of_triangle`: the linear map `u1h_solveLinear e₁ e₂ w₁ w₂ q = (det q e₂ / D) • w₁ +
  (det e₁ q / D) • w₂` (Cramer), `f x = M (x - v0) + w0`.  `U1_isPositiveAffineOn_of_det` is immediate.
* **Pasting.** `U1_continuousOn_iUnion_of_finite` = `(locallyFinite_of_finite C).continuousOn_iUnion`.
* **IsHomeoOnto.** `comp` = `Homeomorph.trans`; `inv` = `Homeomorph.symm` (agreement from the left-inverse
  hypothesis); `restrict` is built by hand (`Homeomorph.mk` on `A ≃ f '' A`, inverse through `e.symm`), using
  `u1h_isHomeoOnto_image : f '' S = S'`; `of_homeomorph` = `Homeomorph.image`; `coe` via the builder
  `u1h_isHomeoOnto_of_inv` (continuous two-sided inverse on the sets) with inverse `planeOf`, continuity of
  `planeOf` on `range some` from `OnePoint.isOpenEmbedding_coe.continuousAt_iff`.

## 3. Helper declarations added (all `u1h_`-prefixed; line numbers in W1_U1.lean)

| line | declaration |
|---|---|
| 272 | `U1_triangle_isCompact` |
| 276 | `U1_triangle_convex` |
| 279 | `u1h_baryA` |
| 283 | `u1h_baryB` |
| 286 | `u1h_bary_eq` |
| 295 | `u1h_det0` |
| 302 | `u1h_det2` |
| 310 | `u1h_det1` |
| 320 | `u1h_convex_det_nonneg` |
| 329 | `u1h_mem_carrier_iff_det` |
| 362 | `u1h_continuous_det` |
| 365 | `u1h_isOpen_det_pos` |
| 369 | `u1h_interior_subset_pos` |
| 399 | `u1h_edge01_ne` |
| 402 | `u1h_edge12_ne` |
| 409 | `u1h_edge20_ne` |
| 417 | `u1h_interior_triangle` |
| 433 | `U1_triangle_interior_nonempty` |
| 442 | `U1_triangle_isDisc` |
| 446 | `U1_square_isDisc` |
| 454 | `U1_mem_carrier_iff_det` |
| 459 | `u1h_det_segment` |
| 465 | `u1h_seg0` |
| 484 | `u1h_seg1` |
| 502 | `u1h_seg2` |
| 522 | `U1_frontier_triangle` |
| 547 | `U1_interior_convex_isConnected` |
| 552 | `u1h_isPreconnected_exterior` |
| 575 | `u1h_isPreconnected_ray` |
| 581 | `U1_compl_compact_convex_isConnected` |
| 621 | `U1_affineOn_comp` |
| 630 | `U1_affineOn_mono` |
| 636 | `u1h_det_linear` |
| 646 | `u1h_vertex_mem_carrier` |
| 650 | `u1h_affineOn_sub` |
| 656 | `U1_isPositiveAffineOn_mono` |
| 667 | `u1h_affineMap` |
| 670 | `u1h_affineMap_apply` |
| 675 | `u1h_affineOn_image_convexHull` |
| 684 | `u1h_image_carrier` |
| 690 | `U1_isPositiveAffineOn_comp` |
| 697 | `u1h_solveLinear` |
| 706 | `u1h_solveLinear_apply` |
| 709 | `u1h_det_self` |
| 712 | `U1_exists_affine_of_triangle` |
| 727 | `U1_isPositiveAffineOn_of_det` |
| 733 | `U1_continuousOn_iUnion_of_finite` |
| 739 | `U1_isHomeoOnto_comp` |
| 749 | `U1_isHomeoOnto_inv` |
| 757 | `u1h_isHomeoOnto_image` |
| 767 | `U1_isHomeoOnto_restrict` |
| 802 | `U1_isHomeoOnto_of_homeomorph` |
| 807 | `u1h_isHomeoOnto_of_inv` |
| 821 | `U1_isHomeoOnto_coe` |

(`U1_*` rows are the leaves; every helper sits immediately before the first leaf that uses it.  Helpers likely
useful to U2-U5: `u1h_mem_carrier_iff_det`/`u1h_interior_triangle` (open triangle formula), `u1h_bary_eq`,
`u1h_seg0/1/2`, `u1h_det_linear`, `u1h_affineOn_image_convexHull`, `u1h_isHomeoOnto_of_inv`,
`u1h_isHomeoOnto_image`, `u1h_isPreconnected_exterior`.)

## 4. Method audit / pitfalls met (reassessment discipline)

No lemma needed more than two attempts; no method change was required.  Friction points, for the next units:
* `field_simp` does not see a determinant denominator once `det` is unfolded: `set D := det … with hDdef` **before**
  unfolding, prove with `D` opaque, then `simp only [hDdef, det, …]; ring`.
* `push_neg` is deprecated under the pin (use `not_or`/`not_not` or `push Not`); `Set.mem_setOf_eq` →
  `Set.mem_ofPred_eq`; `Set.mem_diff` → `Set.mem_sdiff`; `Set.restrict` → `Set.domRestrict`
  (`continuousOn_iff_continuous_domRestrict`); `Set.image_subset` → `Set.image_mono`; `left_mem_Ici` is gone
  (`mem_Ici.2 le_rfl`).
* Mathlib uses the module system (`public import`): `rank_self` is `Module.rank_self` and needs
  `Mathlib.LinearAlgebra.Dimension.StrongRankCondition` imported explicitly; `one_lt_two` fails on `Cardinal`
  (no `AddLeftStrictMono`), use `exact_mod_cast (by norm_num : (1:ℕ) < 1 + 1)`.
* `Set.Finite.isCompact_convexHull` needs `(𝕜 := ℝ)`.
* After `fin_cases i` on `Fin 3`, `simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.reduceAdd,
  zero_add]` normalises `T.v (i + 1)` to `T.v 1`, `T.v 2`, `T.v 0`.

## 5. Black boxes

None: no axioms beyond the standard three, no leaf of another unit consumed, no `sorry` in the U1 block.
