# W2_U7_REPORT.md — unit U7 (57b for the interior region), wave 2

Written 2026-09-19 (12:10 UTC / 8:10am ET) by the U7 agent.  File: `work/drafts/twodiscs/W2_U7.lean`
(= `W1_Assembled.lean` with the U7 block at lines 10783-10997 replaced; 13,989 lines).  Typecheck:
`cd work/lean && lake env lean ../drafts/twodiscs/W2_U7.lean` — **0 errors** (log: scratch `w2u7/full.log`).
Identity: `python3 check_57_identity.py W2_U7.lean` → `IDENTITY OK`.  `grep -c sorry`: **33 → 26** (the 7 U7 leaves).
Everything outside the U7 block is byte-identical to `W1_Assembled.lean` (checked by `diff` on lines 1-10782 and on
every later leaf header); every U7 leaf docstring + statement is byte-identical to the frozen text.

## 1. Result — all 7 leaves closed

| leaf (line in W2_U7.lean) | axioms (`#print axioms`, scratch copy `w2u7/P5ax.lean`) |
|---|---|
| `U7_closure_interiorRegion_eq` 10837 | `[propext, sorryAx, Classical.choice, Quot.sound]` — sorryAx only via the black box `U6_interiorRegion_eq` |
| `U7_isPLDisc_image` 10844 | `[propext, Classical.choice, Quot.sound]` — **sorry-free** |
| `U7_chartPart_cap_empty` 10872 | sorryAx via `U6_exists_ambientParam`, `U6_interiorRegion_eq` |
| `U7_isPositivePLToPlane_inv` 10890 | sorryAx via `U6_interiorRegion_eq` |
| `U7_pl_discs_inner` 10932 | sorryAx via `U6_exists_ambientParam`, `U6_interiorRegion_eq` |
| `U7_isPLDisc_of_isPLDiscSphere` 10950 | `[propext, Classical.choice, Quot.sound]` — **sorry-free** |
| `U7_isPLDisc_closure_interior` 10991 | sorryAx via `U6_exists_ambientParam`, `U6_interiorRegion_eq` |

No `sorry` remains in the U7 block; no rule-3 correction was needed (every leaf is true as stated); no new
interface from another unit was needed.  Once U6 closes `U6_exists_ambientParam` and `U6_interiorRegion_eq`, all seven
become sorry-free with no change to this unit.  Consequences for the row: `U7_pl_discs_inner` (direct field of
`lem_gauss_two_discs`, and consumed by `u10h_pl_discs`, `u11h_pl_disc`), `U7_closure_interiorRegion_eq` (U10
`u10h_circle_subset_closure`) and the two bridges are now closed on the U6 black boxes only.

## 2. What is proved (route, as in W1_ASSEMBLY_REPORT §5 U7)

Witness disc `D = A.T₀.carrier`, parametrisation `f = A.H.symm ∘ planeOf`, for any `A : AmbientParam P L`.

* **Inside the square** (`u7h_supNorm_lt_of_mem_image`, 10793): `w ∈ H '' T₀ → supNorm w < L`.  If `L ≤ supNorm (H x)`
  then `H (H x) = H x` by `A.fix`, so `H x = x` by injectivity and `L ≤ supNorm x`, against
  `x ∈ T₀ ⊆ interior (square L) ⊆ {supNorm < L}` (`A.inside`, `u3h_interior_square_subset`).  Corollaries
  `u7h_image_subset_square`, `u7h_image_isCompact`.
* **Closure** (`u7h_closure_interior_triangle`, `u7h_closure_image_interior`, `u7h_closure_coe_image`, 10815-10835):
  `closure (interior T₀) = T₀` (`Convex.closure_interior_eq_closure_of_nonempty_interior` + closedness),
  `closure (H '' interior T₀) = H '' T₀` (`Homeomorph.image_closure`), and in the sphere
  `closure (coe '' (H '' interior T₀)) = coe '' (H '' T₀)`: `⊆` because `coe '' (H '' T₀)` is closed
  (`OnePoint.isClosed_image_coe`: closed and compact in the plane), `⊇` by `image_closure_subset_closure_image`.
  With `U6_interiorRegion_eq` this is **`U7_closure_interiorRegion_eq`**.
* **`U7_isPLDisc_image`**: `⟨T₀, A.KT, A.H, U1_triangle_isDisc, A.plT, U1_isHomeoOnto_of_homeomorph⟩`.
* **Chart parts** (`u7h_chartPart_plane` 10849, `u7h_chartPart_cap` 10862): the plane chart part of `coe '' (H '' T₀)`
  is `H '' T₀` (coe injective, `u7h_image_subset_square`); the cap chart part is empty: `capChart L y = ↑w` with
  `w ∈ H '' T₀ ⊆ square L`, `y ∈ square 1` forces `supNorm w = L` by `u3h_seam` (needs `0 < L`, from
  `U4_polygonImage_subset_interior_square`), against `supNorm w < L`.  Gives **`U7_chartPart_cap_empty`**.
* **`U7_isPositivePLToPlane_inv`**: chart `false`: rewrite the chart part to `H '' T₀` and the map to `H.symm`
  (`u7h_inv_comp_plane_chart`, `funext; rfl` since `planeOf ↑x = x` definitionally), then
  `U2_inverse_isPositivePLOn A.KT A.H A.plT`.  Chart `true`: the part is `∅`, `U2_triangulation_empty`, and any map is
  positive PL on a triangulation of `∅` (`u7h_isPositivePLOn_empty`: a face would contain its vertex `T.v 0`).
* **`U7_pl_discs_inner`** (10932): `regionOf P .inner` is `interiorRegion P` definitionally; the five clauses are
  `U1_triangle_isDisc`, `u7h_circle_subset` (`sphereCircle P = coe '' (H '' frontier T₀)` by `A.boundary`,
  `frontier T₀ ⊆ T₀`), `u7h_isHomeoOnto_inv` (`U1_isHomeoOnto_coe` inverted by `planeOf` with `U1_isHomeoOnto_inv`,
  composed with `U1_isHomeoOnto_of_homeomorph` inverted by `H.symm`, via `U1_isHomeoOnto_comp`), `u7h_image_circle`
  (`(H.symm ∘ planeOf) '' (coe '' (H '' frontier T₀)) = frontier T₀` by `image_image` twice and `H.symm (H x) = x`),
  and `U7_isPositivePLToPlane_inv`.
* **`U7_isPLDisc_of_isPLDiscSphere`** (bridge, 10950): from `IsPLDiscSphere L S B` take `D, f`; invert with
  `U3_isPositivePLFromPlane_inv hL hD hf hpl` to get `g : Plane → Sphere` positive PL from the plane on a
  triangulation `K` of `D`, with `g (f z) = z` on `S`.  `g '' D ⊆ S` follows from `f '' S = D`
  (`u1h_isHomeoOnto_image`) and `g ∘ f = id` on `S`.  Witness for `IsPLDisc (coe ⁻¹' S)`: `⟨D, K, planeOf ∘ g⟩`.
  Positive PL: a face read in the plane chart is exactly `planeOf ∘ g` (definitional); a face `T` read in the **cap**
  chart is impossible — every `x ∈ T` has `g x = capChart L y₁ = ↑w` with `y₁ ∈ square 1`, `w ∈ square L` (from
  `hS`), so `u3h_seam` gives `w = capInvFun L y₁`, `supNorm y₁ = 1`, hence `(capInvFun L ∘ g) x = y₁` lies on the
  seam, and a nondegenerate triangle cannot lie in `{supNorm = 1}` (`u7h_not_subset_seam`, 10943: its interior point
  has `supNorm < 1` by `u3h_interior_square_subset`).  Homeomorphism: `IsHomeoOnto (coe ⁻¹' S) S coe`
  (`U1_isHomeoOnto_coe` + `image_preimage_eq_of_subset`), composed with `hf`, inverted by `planeOf ∘ g`
  (`U1_isHomeoOnto_inv`).
* **`U7_isPLDisc_closure_interior`** (10991): `U4_exists_insideModel`, `U6_exists_ambientParam`,
  `U7_closure_interiorRegion_eq`, `preimage_image_eq _ coe_injective`, `U7_isPLDisc_image`.

## 3. Black boxes consumed (other units' leaves, used by name as they stand)

* U6 (open, sorry): `U6_exists_ambientParam`, `U6_interiorRegion_eq`.  (`U6_exteriorRegion_eq` was listed in the
  spec but is not needed.)
* U1 (closed): `U1_triangle_isCompact`, `U1_triangle_convex`, `U1_triangle_interior_nonempty`, `U1_triangle_isDisc`,
  `U1_isHomeoOnto_comp`, `U1_isHomeoOnto_inv`, `U1_isHomeoOnto_of_homeomorph`, `U1_isHomeoOnto_coe`, helper
  `u1h_isHomeoOnto_image`.
* U2 (closed): `U2_inverse_isPositivePLOn`, `U2_triangulation_empty`, helpers `u2h_carrier_subset`, `u2h_map_carrier`.
* U3 (closed): `U3_isPositivePLFromPlane_inv` (the corrected form with `hL : 0 < L`), helpers `u3h_seam`,
  `u3h_capInvFun_capInvFun`, `u3h_interior_square_subset`.
* U4 (closed): `U4_polygonImage_subset_interior_square`, `U4_exists_insideModel`.
* Mathlib (pin): `Convex.closure_interior_eq_closure_of_nonempty_interior`, `Homeomorph.image_closure`,
  `OnePoint.isClosed_image_coe`, `OnePoint.coe_injective`, `OnePoint.continuous_coe`,
  `image_closure_subset_closure_image`, `image_preimage_eq_of_subset`, `preimage_image_eq`.

## 4. Method audit

No lemma needed more than one failed attempt.  Two compile rounds on scratch pieces (`w2u7/P1..P5.lean`, each
against the prefix olean `w2u7/pfx/W2U7Prefix.olean` = `W1_Assembled.lean:1-10782` + `end SM`, ~20 s per piece):
round 1 fixed two membership ascriptions (`hw : w ∈ modelChart L false ⁻¹' _` had to be restated as
`(↑w : Sphere) ∈ coe '' _` by an explicit type on `obtain`); round 2 fixed one orientation of an equation
(`u3h_seam` wants `↑w = capChart L y`, which the image witness already provides).  `push_neg` (deprecated in the
pin) was replaced by `not_lt.1`.  Wave-1 pitfalls observed: `Link.IsDisc` is reached as `Link.IsDisc` inside
`namespace SM` (no `open Link`); `planeOf ↑x = x` and `modelChart L false x = ↑x` are `rfl` but need `show`/type
ascriptions when they sit inside a membership hypothesis; `Nat.card` and `open Topology` did not arise.

## 5. Notes for other units / U12

* For U6: this unit relies on exactly the two statements `U6_exists_ambientParam` and `U6_interiorRegion_eq` as they
  stand; no other U6 clause is used.  U11's `u11h_circle_subset_closure` becomes independent of U7 as soon as U6
  proves `U6_interiorRegion_eq` (see W1_ASSEMBLY_REPORT §5 U6 note) — unchanged here.
* For U8: `u7h_supNorm_lt_of_mem_image`, `u7h_image_subset_square`, `u7h_chartPart_plane` and `u7h_not_subset_seam`
  are generic enough to be reused (the last one for ruling out seam faces in `U8_isPositivePLSphereMap_inv`).
* For U12: no `set_option`, no `#print`, no new imports; warnings only (unused `hn`, `hP` in leaves whose frozen
  statements carry them, and the pre-existing wave-1 ones).
