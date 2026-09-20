# W1_U2 — unit U2 (triangulation basics) of row 57 `lem_gauss_two_discs`: REPORT

Written 2026-09-19 by the U2 prover.  File: `work/drafts/twodiscs/W1_U2.lean` (copy of `Skeleton_FINAL.lean`
with the 17 `U2_*` leaf bodies filled in and `u2h_`-prefixed helpers inserted immediately before the leaf that
first uses them).  Typecheck: `cd work/lean && lake env lean ../drafts/twodiscs/W1_U2.lean` → **0 errors**,
75 `sorry` warnings (= the 75 leaves of the other units, untouched).  `python3 work/drafts/twodiscs/check_57_identity.py
work/drafts/twodiscs/W1_U2.lean` → `IDENTITY OK`.  `grep -c sorry`: Skeleton_FINAL 95 → W1_U2 78 (the 17 U2 leaf
`sorry`s removed; the remaining 78 = 75 leaves + 3 mentions in comments).  No leaf statement, name or docstring was
changed; no statement of another unit was touched; no new `u2h_` Prop with `sorry` was needed (rule 2/3 not
invoked).  Two imports were added at the top (allowed by SKELETON_REPORT §0):
`Mathlib.Topology.Algebra.Module.FiniteDimension` (continuity of linear maps of the plane) and
`Mathlib.Analysis.Normed.Module.Connected` (`isConnected_sphere`).

## 1. Closed leaves (17/17 of U2; the leaf table of SKELETON_REPORT §2 lists 17 `U2_` rows)

| leaf | method |
|---|---|
| `U2_isCompact_of_triangulation` | finite union of compact faces (`Set.Finite.isCompact_biUnion`, `U1_triangle_isCompact`) |
| `U2_triangulation_empty` | `faces := ∅` |
| `U2_triangulation_triangle` | `faces := {T}`; `inter` by `u2h_carrier_inter_self` |
| `U2_triangulation_square` | two faces `(-L,-L),(L,-L),(L,L)` and `(-L,-L),(L,L),(-L,L)`; membership by `U1_mem_carrier_iff_det` + `nlinarith`; `inter` = the diagonal segment (`convexHull_pair`, `segment_eq_image`) |
| `U2_isPositivePLOn_of_refines` | `U1_isPositiveAffineOn_mono` |
| `U2_refine_fan` | faces `= {T' ∈ K.faces | T'.carrier ≠ T.carrier} ∪ range (fan i)` with fan `i = (T.v i, T.v (i+1), o)`; cover by the sign pattern of `d_i = det (T.v i - o) (x - o)` (identity `c₀₁d₂ + c₂₀d₁ + c₁₂d₀ = 0`); `inter` fan/fan by the spoke functional (F2), fan/old face by the sub-triangle lemma `u2h_inter_sub` |
| `U2_refine_edge_split` | faces `= old ∪ {(T.v i, p, T.v (i+2)), (p, T.v (i+1), T.v (i+2))}`; cover by the sign of `det (T.v (i+2) - p) (x - p)`; `inter` via `u2h_inter_sub'` with the case analysis on the common face `S` (the case `S ⊆ {v_i, v_(i+1)}` uses `huniq`) |
| `U2_exists_ball_disjoint_faces` | `x ∉` the closed finite union of the faces missing `x`; `Metric.isOpen_iff` on its complement |
| `U2_local_structure` | from the previous leaf |
| `U2_edgeSeg_subset_frontier` | open edge ⊆ frontier (every face through a point of the open edge contains the edge, `u2h_edge_subset_of_openSegment_mem`, hence has carrier `T.carrier` by `huniq`; a point of the ball on the outer side of the edge line lies outside `X` by `U2_local_structure`), then `closure_openSegment` and `closure_minimal` |
| `U2_interior_face_subset_interior` | `interior_mono` |
| `U2_openSegment_subset_interior_of_two_faces` | `u2h_reversed_edge` (a second face containing an edge carries it reversed) + `u2h_ball_subset_two_faces` (near a point of the open edge the plane is covered by the two faces) |
| `U2_frontier_eq_iUnion_boundary_edges` | ⊇ from `U2_edgeSeg_subset_frontier`; ⊆: a frontier point lies in no open face and on no doubly covered open edge, so it is a vertex of every face through it with every edge at it doubly covered; the vertex-star lemma `u2h_mem_interior_of_vertex_star` then makes it interior (contradiction) |
| `U2_pushforward` | `faces := range (T ↦ T.map H _)`; `H '' convexHull S = convexHull (H '' S)` on a face (`AffineMap.image_convexHull`), `image_inter` by injectivity |
| `U2_inverse_isPositivePLOn` | the strengthened pushforward `u2h_pushforward` (faces are literally `T.map H _`); `H.symm` agrees on `H '' T.carrier` with the affine map `g` of `U1_exists_affine_of_triangle` sending `H (T.v k) ↦ T.v k`, because `g ∘ H` and `id` are affine on `T.carrier` and agree on the vertices (`u2h_affineOn_eq_of_vertices`) |
| `U2_isHomeoOnto_of_isPositivePLOn` | `Equiv.Set.imageOfInjOn` + `Continuous.homeoOfEquivCompactToT2` |
| `U2_continuousOn_of_isPositivePLOn` | `U1_continuousOn_iUnion_of_finite` over the faces (`biUnion_eq_iUnion`), affine maps continuous |

## 2. Helpers (108 `u2h_` declarations)

Toolbox (before `U2_triangulation_square`): `det` algebra (`u2h_det_def`, `u2h_pos_cyc` cyclic positivity,
`u2h_mem_iff` cyclic membership, `u2h_range_v`, `u2h_v_ne`), barycentric coordinates from the `det` criterion
(`u2h_bary`, `u2h_mem_of_bary`, `u2h_det_affine`), interior criteria (`u2h_mem_interior_of_det_pos`,
`u2h_det_pos_of_mem_interior`: strict `det` conditions ⟺ interior point), open/closed half-planes.
Face lemmas (before `U2_refine_fan`): `Fin 3` arithmetic (`u2h_fin3_cases`, `u2h_fin3_add_*`), A
(`u2h_vertex_mem_of_mem_convexHull`), B (`u2h_convexHull_subset_edge_of_notMem`), D
(`u2h_carrier_eq_of_range_subset`, via `Set.ncard`), E1 (`u2h_det_eq_zero_of_mem_segment`), F1/F2/F3
(`u2h_eq_vertex_of_det_eq_zero`, `u2h_mem_segment_of_det_eq_zero`, `u2h_det_nonneg/nonpos_on_carrier`), the
sub-triangle `inter` lemma `u2h_inter_sub` (and `u2h_inter_sub'`).  Then the fan (`u2h_fanT`, `u2h_fan_cover`,
`u2h_fan_inter_succ`, `u2h_fan_inter_old`), the split (`u2h_spT1/2`, `u2h_sp_cover`, `u2h_sp_inter`,
`u2h_sp_inter_old`, `u2h_edge_subset_of_openSegment_mem`), affine images (`u2h_image_convexHull_of_affineOn`,
`u2h_map_carrier`, `u2h_pushforward`, `u2h_affineOn_eq_of_vertices`), the frontier lemmas (`u2h_reversed_edge`,
`u2h_ball_subset_two_faces`, `u2h_exists_det_neg_in_ball`) and the vertex star (`u2h_cone`, `u2h_star_open_at`,
`u2h_mem_interior_of_vertex_star`).

## 3. Black boxes consumed (U1 leaves, still `sorry` in this file by rule 2)

`U1_affineOn_comp`, `U1_affineOn_mono`, `U1_continuousOn_iUnion_of_finite`, `U1_exists_affine_of_triangle`, `U1_frontier_triangle`, `U1_isPositiveAffineOn_mono`, `U1_mem_carrier_iff_det`, `U1_triangle_convex`, `U1_triangle_isCompact`.

`#print axioms` (scratch copy `W1_U2_axioms.lean`): `U2_triangulation_empty`, `U2_triangulation_triangle`,
`U2_interior_face_subset_interior` depend on `[propext, Classical.choice, Quot.sound]` only; the other 14 leaves
additionally on `sorryAx`, which enters only through the consumed U1 leaves above (every `u2h_` helper and every
U2 body is `sorry`-free).

## 4. Method notes / pitfalls for the next units

* The `det` criterion `U1_mem_carrier_iff_det` *is* barycentric coordinates (`u2h_bary`): `μ = d/D` with
  `d₀ + d₁ + d₂ = D`.  Most "face" arguments reduce to F1/F2/F3 with an affine functional `det a (· - q)`.
* Two faces sharing an edge carry it with opposite orientation (`u2h_reversed_edge`); the same-orientation case is
  refuted by a point `(1-t)·midpoint + t·w` in both faces off the edge line, `t` from `nhdsWithin 0 (Ioi 0)`
  (`ContinuousAt.eventually_lt`, `Ioo_mem_nhdsGT`).  Use plain `nhdsWithin`/`nhds`: the unit file does not
  `open Topology`, so `𝓝[>]` does not parse there.
* Vertex-star (master lemma): the covered unit directions `{d | ∃ T j, T.v j = x ∧ x + d ∈ cone T j} ∩ S¹` are
  closed (finite union) and open at every nonzero direction (interior of a cone, or a boundary ray: the doubly
  covering face's cone takes over), hence all of `S¹` by `isConnected_sphere` (`1 < Module.rank ℝ Plane` via
  `Module.finrank_prod`) and `isClopen_iff` on the subtype.  Then `y ∈ cone` by scaling, and `y ∈ T` as soon as the
  opposite-edge functional is positive, an open condition at `x`.
* Structure-instance fields after a line break must be indented past the opening `{`; `simp` on `![a,b,c] k`
  needs the full simp set (`Matrix.cons_val_two` alone leaves `vecHead (vecTail …)`).
* Reassessment discipline: no lemma needed two failed attempts.  One method change: the first sub-triangle `inter`
  lemma (`u2h_inter_sub`, hypothesis "U meets any unspanned edge of T only in its vertices") does not cover the edge
  split (the half `(v_i, p, v_(i+2))` meets edge `i` in `[v_i, p]`), so `u2h_inter_sub'` leaves the case analysis on
  the common face to the caller; both are kept (the fan uses the first).

## 5. Rule 3 / statement issues

None: every U2 leaf is true as stated and closed without modification.
