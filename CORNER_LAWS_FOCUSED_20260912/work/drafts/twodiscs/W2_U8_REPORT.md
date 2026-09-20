# Row 57 lem:gauss-two-discs — wave 2, unit U8 (57b for the exterior region): `W2_U8.lean`

Written 2026-09-19 by the U8 executor.  Start file: `W1_Assembled.lean` (13 815 lines); result: **`W2_U8.lean`**
(17 167 lines, +3 352).  Scratch (private): `/workspace/scratch/claude-0/-workspace-repos-lean/
d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/w2u8/` (`pfx/` = prefix oleans of the frozen prelude and of the
finished pieces, `t/` = the pieces `t1…t5, f1…f10c`, `assemble.py`, `W2_U8_axioms.lean`, `compile_*.log`).

## 0. Result

| check | result |
|---|---|
| `cd work/lean && lake env lean ../drafts/twodiscs/W2_U8.lean` | **0 errors**, 22 `declaration uses sorry` warnings (= the 22 open leaves of U5/U6/U7/U9), 87 linter/deprecation warnings (40 inherited from `W1_Assembled`, 47 in the U8 block, §7); 54 s wall (`compile_full.log`) |
| `python3 check_57_identity.py W2_U8.lean` | `IDENTITY OK` |
| `grep -c sorry` | 33 (`W1_Assembled`) → **25** (`W2_U8`) = 22 open leaves of U5/U6/U7/U9 + 3 docstring mentions; **no `sorry` in any U8 leaf or `u8h_` helper** |
| U8 leaves | **8/8 closed**: `U8_capInvFun_capInvFun`, `U8_supNorm_capInvFun`, `U8_capChart_isHomeoOnto`, `U8_capInvFun_seam`, `U8_exists_exterior_fan`, `U8_closure_exteriorRegion_eq`, `U8_isPositivePLSphereMap_inv`, `U8_pl_discs_outer`; statements, names and docstrings untouched |
| `#print axioms` (scratch copy `W2_U8_axioms.lean`, 12 declarations) | `U8_capInvFun_capInvFun`, `U8_supNorm_capInvFun`, `U8_capChart_isHomeoOnto`, `U8_capInvFun_seam`, **`U8_exists_exterior_fan`**, and the helpers `u8h_gS_isHomeoOnto`, `u8h_g_bij`, `u8h_src_straight`, `u8h_f_fan_triangulation`: `[propext, Classical.choice, Quot.sound]` (sorry-free); `U8_closure_exteriorRegion_eq`, `U8_isPositivePLSphereMap_inv`, `U8_pl_discs_outer`: additionally `sorryAx`, entering only through the U6 black boxes `U6_exteriorRegion_eq` / `U6_exists_ambientParam` (§6).  No literature axiom, no `native_decide`, no unregistered axiom; no `#print` left in the unit file |
| helpers | 251 `u8h_`-prefixed declarations (of which 73 are `u8h_f_` copies of U10's fan toolkit, §4), placed between the `### U8` section header and the first U8 leaf, except the sphere-level assembly `u8h_cap_eq … u8h_gS_isHomeoOnto` (between `U8_capInvFun_seam` and `U8_exists_exterior_fan`, since it uses the closed leaf `U8_capChart_isHomeoOnto`) and `u8h_closure_ext_mem_coe` (between `U8_closure_exteriorRegion_eq` and `U8_isPositivePLSphereMap_inv`, which uses it); two closed namespaces `u8h_AnnCtx`, `u8h_AnnData` with `variable … include`; 6 `open Classical in` scoped to one declaration each |

## 1. What is proved, leaf by leaf

* **`U8_capInvFun_capInvFun`, `U8_supNorm_capInvFun`, `U8_capInvFun_seam`** — one line each from U3's chart algebra
  (`u3h_capInvFun_capInvFun hL.ne'`, `u3h_supNorm_capInvFun`, `u3h_capInvFun_seam`).
* **`U8_capChart_isHomeoOnto`** — `u1h_isHomeoOnto_of_inv` with inverse `modelChartInv L true`.  Continuity of
  `capChart L` on `Q_1`: at `y ≠ 0` it is `coe ∘ capInvFun L` (`u8h_continuousAt_capInvFun`); at `0` it tends to
  `∞` through `OnePoint.hasBasis_nhds_infty` (a closed compact set is sup-norm bounded by some `R`, and
  `‖capInvFun L y‖_∞ = L/‖y‖_∞ > R` for `‖y‖_∞ < L/(R+1)`).  Continuity of the inverse: at `∞` via
  `OnePoint.continuousAt_infty'` and `capInvFun L → 0` along `coclosedCompact` (`u8h_tendsto_capInvFun_cocompact`),
  at finite points via `OnePoint.continuousAt_coe`.  Maps-to and the two inverse identities are `u3h_chartInv_chart`,
  `u3h_capInvFun_capInvFun`, `u3h_supNorm_capInvFun`.
* **`U8_closure_exteriorRegion_eq`** — from `U6_exteriorRegion_eq` (black box): `coe '' (H '' int T₀)` is open
  (`OnePoint.isOpen_image_coe`, `H.isOpenMap`), so its complement is a closed superset of the exterior region;
  conversely a finite point `coe y` of the complement has `H.symm y ∈ closure T₀ᶜ` (`closure_compl`), whence
  `y ∈ closure (H '' T₀ᶜ)` (`Homeomorph.image_closure`) and `coe y ∈ closure (coe '' (H '' T₀ᶜ))`.
* **`U8_exists_exterior_fan`** — the witness is `u8h_gS hL T₀ hT : Sphere → Plane`, `∞ ↦ 0`,
  `coe x ↦ if ‖x‖_∞ ≤ L then g_A x else capInvFun L x`, where `g_A` is the annulus map of §2.  Read in the cap chart
  it is the identity of `Q_1` (`u8h_gS_capChart`: on the seam `g_A = ρ_L = capInvFun L`, `u8h_g_seam`,
  `u8h_capInvFun_eq_ρ`); read in the plane chart it is `g_A`, positive PL on the annulus triangulation `u8h_K`
  (`u8h_gS_isPositivePLToPlane`; `chartPart L false E = Q_L \ int T₀`, `chartPart L true E = Q_1`).  Homeomorphism
  onto `Q_2` by compactness (`u8h_isHomeoOnto_of_compact`: `E` is closed in the compact sphere, `gS` is continuous
  on `E = coe '' (Q_L \ int T₀) ∪ (coe '' {L ≤ ‖·‖_∞} ∪ {∞})` by the pasting lemma `ContinuousOn.union_of_isClosed`,
  injective — cross-injectivity between the annulus part and the cap reduces to the seam (`u8h_cap_seam_case`) —
  and onto: `g_A '' (Q_L \ int T₀) = Q_2 \ int Q_1` and the cap goes to `Q_1`).  Boundary clause:
  `g_A '' ∂T₀ = ∂Q_2` (`u8h_g_frontier`, §2).
* **`U8_isPositivePLSphereMap_inv`** — `F = OnePoint.map A.H.symm`.  Plane chart: `chartPart L false (closure ext)
  = H '' (Q_L \ int T₀)` (`u8h_H_image_square`, `A.fix`); the fan leaf's plane-chart triangulation of
  `Q_L \ int T₀` is refined into `A.K` (`U3_refine_into`) so that `H` is positive PL on it, and pushed forward by
  `U2_inverse_isPositivePLOn`; the target chart is the plane chart and `modelChartInv L false ∘ F ∘ coe = H.symm`.
  Cap chart: `chartPart L true (closure ext) = Q_1` (`u8h_chartPart_true_eq`), `U2_triangulation_square`, and
  `F ∘ capChart L = capChart L` because `H.symm` fixes `{L ≤ ‖·‖_∞}` (`u8h_H_symm_fix`), so the read map is the
  identity.  `IsHomeoOnto`: `F` is the homeomorphism `Homeomorph.onePointCongr A.H.symm`
  (`u8h_isHomeoOnto_onePoint_map`) and `F '' closure ext = (coe '' int T₀)ᶜ` (`Set.image_compl_eq`).
* **`U8_pl_discs_outer`** — witness `D = square 2`, `f = g ∘ OnePoint.map A.H.symm` with `A` from
  `U6_exists_ambientParam` and `g` from `U8_exists_exterior_fan`: `U1_square_isDisc`; `sphereCircle P =
  coe '' (H '' ∂T₀) ⊆ closure ext` (via `U8_closure_exteriorRegion_eq`); `U1_isHomeoOnto_comp`;
  `f '' sphereCircle P = g '' (coe '' ∂T₀) = ∂Q_2`; `U3_isPositivePLToPlane_comp`.

## 2. The exterior fan (method)

The plan's 11-ray fan is realised **order-free**: no cyclic sorting of the rays is ever done.
1. **Radial annulus triangulation** (`u8h_AnnData.triangulation`, generic): for nested convex discs `Din ⊆ int Dout`
   with a centre `z ∈ int Din`, a finite set `V` of marks on `∂Dout`, an adjacency relation `A ⊆ u8h_f_Adj`
   covering `∂Dout` (the hypotheses of U10's `u10h_fan_triangulation`) and *straightness* of `∂Din` between the
   radial projections `Pt a, Pt b` of adjacent marks, the faces `(Pt a, a, b)` and `(Pt a, b, Pt b)` over all
   adjacent pairs form a `Triangulation (Dout \ interior Din)`.  Sector coordinates `x − z = α(a−z) + β(b−z)`
   (`u8h_α, u8h_β`, Cramer) make both gauges linear on a sector (`u8h_rg_sector`) and describe the two faces by
   linear inequalities (`u8h_mem_tri2_iff`, `u8h_mem_tri1_iff`, `u8h_quad_iff`).  Cover: from the fan
   triangulation of `Dout`.  Face-to-face intersections: `u3h_inter_of_family` with separation by
   `u3h_faces_separated` of the fan faces (different fan faces) or by the common diagonal (same pair), and the
   vertex condition by the sector lemma `u8h_f_frontier_mem_segment` (a vertex of a face lying in another is an
   outer mark or a radial projection of one, hence equals a vertex).
2. **Gluing by choice** (`u8h_glue`, generic): from a vertex assignment `w` the face-wise affine maps
   `U1_exists_affine_of_triangle` are glued into one function; two face maps agree on a common face because affine
   maps agreeing on the common vertices agree on their convex hull (`u8h_affine_eq_on_hull`).  Positivity is the
   `det` sign of the vertex images (`u8h_glue_isPositivePLOn`).
3. **Bijection lemma** (`u8h_bij_of_faces`, generic): a face-wise positive affine map carrying the faces of `K`
   onto faces of `K'`, surjectively on faces and injectively on vertices, is a bijection of the carriers
   (`K'.inter` reduces a collision to a common face, where positive affine maps are injective).
4. **Instances**: source `(z, Din, Dout) = (o₀, T₀, Q_L)` with marks `V` = corners of `Q_L` ∪ the outer projections
   `q_i` of the vertices of `T₀` (the four sides and the three degenerate pieces `(q_i, q_i)` as the `Finset` of
   frontier pieces, so `u10h_cover` applies verbatim); target `(0, Q_1, Q_2)` with marks `ρ_{L/2}(V) ⊆ ∂Q_2`
   (`ρ_L x = (x₁/L, −x₂/L)`, `ρ_{L/2} = 2ρ_L`) and the reversed adjacency `A' (ρ_{L/2} b) (ρ_{L/2} a) :⟺ A a b`.
   The vertex map is `w a = ρ_L a` on outer marks and `w (Pt a) = ρ_{L/2} a`; the face `(Pt a, a, b)` goes onto the
   target face `(Pt' (ρ_{L/2} b), ρ_{L/2} a, Pt' (ρ_{L/2} a))` and `(Pt a, b, Pt b)` onto
   `(Pt' (ρ_{L/2} b), ρ_{L/2} b, ρ_{L/2} a)` (`u8h_g_himg`, `u8h_g_hsurj`), with `det a b > 0` about the origin by
   sign-constancy over the interior (`u8h_det_sign_const`).
5. **Straightness of `∂T₀`** (`u8h_src_straight`): the only place where the triangle enters.  For adjacent outer
   marks `a, b`, take the inner frontier point `y` on the bisecting ray; the fan cover of `T₀` (marks = vertices and
   the inner projections of all outer marks) gives an inner-adjacent pair `(Pt a', Pt b')` containing `y`; four
   `det` steps with the Cramer expansion `u8h_cramer_det` and the no-mark-inside conditions of both adjacencies force
   `a' = a`, `b' = b` (`u8h_eq_of_det_zero`), so `[Pt a, Pt b] ⊆ ∂T₀`.

## 3. Black boxes consumed (by name, statements untouched)

Wave-2 leaves: `U6_exists_ambientParam`, `U6_exteriorRegion_eq`.  Wave-1 leaves: `U1_exists_affine_of_triangle`,
`U1_frontier_triangle`, `U1_isHomeoOnto_coe/_comp/_inv`, `U1_isPositiveAffineOn_mono/_of_det`,
`U1_mem_carrier_iff_det`, `U1_square_isDisc`, `U1_triangle_convex/_isCompact/_isDisc/_interior_nonempty`,
`U2_continuousOn_of_isPositivePLOn`, `U2_inverse_isPositivePLOn`, `U2_triangulation_square`,
`U3_isPositivePLToPlane_comp`, `U3_refine_into`.  Helpers of other units: 25 `u3h_` (chart algebra
`u3h_capInvFun_*`, `u3h_supNorm_*`, `u3h_chartInv_chart`, `u3h_seam`-family, the gluing criterion
`u3h_inter_of_family`, `u3h_faces_separated`, `u3h_carrier_subset_le/_ge`, `u3h_image_carrier`,
`u3h_isPositiveAffineOn_congr`, `u3h_range_eq_of_carrier_eq`, `u3h_detM_pos`, `u3h_exists_linear_inverse`,
`u3h_dir`, `u3h_det_eq_planeDot`, …), `u1h_isHomeoOnto_of_inv`, `u1h_isHomeoOnto_image`,
`u2h_image_convexHull_of_affineOn`.  No new interface Prop was needed from any other unit.

## 4. The `u8h_f_` copy of U10's fan toolkit (for U12)

`U8` precedes `U10` in the frozen order, so U10's order-free fan development (`u10h_D0 … u10h_fan_triangulation`,
W1_Assembled.lean 10 960-11 563, and `u10h_gap … u10h_cover`, 11 737-11 940) could not be referenced.  It is
polygon-free and depends only on U1-U3, so it was **copied verbatim with `u10h_` → `u8h_f_`** (73 declarations,
≈ 815 lines).  U12 can dedupe by moving U10's block (and nothing else: `CyclicPos`, `IsFinitePLOnFrontier`,
`PreservesCyclicPos` are not used by the copy) before U8, or by replacing every `u8h_f_` by `u10h_` after the move;
the two versions are byte-identical modulo the prefix.  Everything else in U8 is new.

## 5. Method audits (reassessment discipline)

* *Route choice.* The first idea — `U10_fan_extension` on three convex pieces of the annulus — was dropped before
  any Lean: each piece's frontier would have to be produced as an explicit `Finset` of segments with a
  case-dependent number of corners, and the three piece maps would still have to be glued.  The direct 11-ray fan
  with sorted rays was dropped for the same reason (interleaving of 3 vertex rays with 4 corner rays).  The
  order-free formulation of §2 needs no case analysis anywhere; its cost is the copied toolkit.
* *`u8h_src_straight`.* A first plan by case analysis on which edges of `T₀` contain `Pt a`, `Pt b` needed angular
  transitivity with wrap-around exclusions; replaced by the bisecting-ray anchor `y` (§2.5), where every step is
  a two-term Cramer expansion.  Two compile iterations: `linarith` needed the signs of both terms spelled out
  (Step 2), and `set`-abbreviations (`Pt`, `o`) had to be unfolded because `rw` does not see through `let`-bound
  abbreviations after `obtain … rfl`.
* *`u8h_AnnData` bookkeeping.* `extends u8h_AnnCtx` produced no usable parent projection for a `Prop` structure
  with only `Prop` fields; replaced by an explicit field `ctx`.  The sector coordinates were moved out of the
  namespace (`u8h_α z a b x`) because `include`d variables are not added to `def`s.
* Everything else compiled in one or two iterations; no lemma needed a third attempt.

## 6. Remaining `sorry` (none in U8)

The 22 open leaves are U5 (2), U6 (8), U7 (7), U9 (5), unchanged.  `U8_pl_discs_outer`, `U8_isPositivePLSphereMap_inv`
and `U8_closure_exteriorRegion_eq` depend on the U6 black boxes `U6_exists_ambientParam` / `U6_exteriorRegion_eq`, so
their `#print axioms` show `sorryAx` until U6 lands; the five other U8 leaves (including the fan) are sorry-free.

## 7. Notes for U12

* Deprecation warnings (`Set.mem_setOf_eq`, `if_pos`, `ContinuousOn.restrict`, `continuousOn_iff_continuous_restrict`,
  `Set.image_diff`) and unused-`simp`-argument linter notes in the copied block; nothing blocking.
* `u8h_o T₀ := Classical.choose (U1_triangle_interior_nonempty T₀)`; `u8h_K`, `u8h_K'` are `Classical.choose` of the
  triangulation existentials; `u8h_glue` uses `open Classical in` for the membership decision.
* Sizes: fan toolkit copy 815 lines, sector/annulus triangulation ≈ 900, glue/bijection ≈ 120, square/ρ/instances
  ≈ 700, straightness ≈ 220, map and bijection ≈ 330, sphere assembly ≈ 330.
