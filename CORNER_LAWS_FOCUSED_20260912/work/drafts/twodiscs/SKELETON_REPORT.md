# Row 57 lem:gauss-two-discs — SKELETON REPORT

Written 2026-09-19 by the skeleton agent.  Files (all in `work/drafts/twodiscs/`):
* `Skeleton_FINAL.lean` — `Statements_FINAL.lean` (frozen) + 92 leaf statements (all `sorry`) + the assembly of
  `lem_gauss_two_discs` and of the three consumer bridges from the leaves.  Typecheck:
  `cd work/lean && lake env lean ../drafts/twodiscs/Skeleton_FINAL.lean` → **0 errors, 92 `sorry` warnings** (one per leaf;
  the row theorem and the bridges carry no `sorry` of their own).  1 039 lines.
* `check_57_identity.py` — asserts the frozen blocks (definitions §1-§4, the bundle `GaussTwoDiscsData`, the row-theorem
  header) are byte-identical in `Skeleton_FINAL.lean` and in any unit file (`python3 check_57_identity.py [files]`; no
  arguments = Skeleton + `U*.lean`/`Unit*.lean` here; exit 0 iff identical).  Tested: passes on the skeleton, fails on a
  one-byte mutation of the theorem header.
* Extra imports over the frozen file: `SM.DeletedTuple` (for `deleteVertex`, U4/U5) and `Mathlib.Analysis.Convex.Gauge`
  (U11).  Imports are not part of the identity check; unit files may add imports.

## 1. How the row closes

`lem_gauss_two_discs` (line 1008) is proved by
```
refine ⟨U6_two_regions hn P hP, ?_, ?_, ?_, U6_exterior hn P hP⟩
· intro s L hL; cases s with | inner => U7_pl_discs_inner … | outer => U8_pl_discs_outer …
· intro …; exact U10_pl_extension …
· intro …; exact U11_top_extension …
```
Bridges: `two_regions_plane := U6_two_regions_plane`, `isPLDisc_of_isPLDiscSphere := U7_isPLDisc_of_isPLDiscSphere`,
`isPLDisc_closure_interior := U7_isPLDisc_closure_interior`.  So the **six output leaves** that close the row are
`U6_two_regions, U6_exterior, U7_pl_discs_inner, U8_pl_discs_outer, U10_pl_extension, U11_top_extension`; the other 86
leaves are the internal structure each unit proves them from (they are the unit's contract with its dependants, e.g.
`AmbientParam`, `U3_isPositivePLSphereMap_comp`, `U9_lift_preserves_cyclicPos`).  A unit may prove its output leaf by
any route as long as the leaves other units *consume* keep their statements.

New auxiliary vocabulary introduced by the skeleton (not in the frozen file; units may use freely):
`Triangle.map`, `Triangulation.Refines` (U1 section), `Triangle.edgeSeg` (U2), `IsPositivePLFromPlane` (U3), `earHull`
(U4), `structure AmbientParam P L` (U6: `T₀ H K KT pl plT fix inside boundary`), `leftNormal`, `InteriorOnLeft`,
`CyclicPos` (U9), `IsFinitePLOnFrontier`, `PreservesCyclicPos` (U10).

## 2. Leaf table (line numbers in Skeleton_FINAL.lean)

| line | leaf | unit |
|---|---|---|
| 269 | `U1_triangle_isCompact` | U1 |
| 273 | `U1_triangle_convex` | U1 |
| 277 | `U1_triangle_interior_nonempty` | U1 |
| 281 | `U1_triangle_isDisc` | U1 |
| 285 | `U1_square_isDisc` | U1 |
| 289 | `U1_mem_carrier_iff_det` | U1 |
| 295 | `U1_frontier_triangle` | U1 |
| 300 | `U1_interior_convex_isConnected` | U1 |
| 306 | `U1_compl_compact_convex_isConnected` | U1 |
| 311 | `U1_affineOn_comp` | U1 |
| 316 | `U1_affineOn_mono` | U1 |
| 321 | `U1_isPositiveAffineOn_mono` | U1 |
| 326 | `U1_isPositiveAffineOn_comp` | U1 |
| 332 | `U1_exists_affine_of_triangle` | U1 |
| 338 | `U1_isPositiveAffineOn_of_det` | U1 |
| 344 | `U1_continuousOn_iUnion_of_finite` | U1 |
| 350 | `U1_isHomeoOnto_comp` | U1 |
| 356 | `U1_isHomeoOnto_inv` | U1 |
| 362 | `U1_isHomeoOnto_restrict` | U1 |
| 368 | `U1_isHomeoOnto_of_homeomorph` | U1 |
| 373 | `U1_isHomeoOnto_coe` | U1 |
| 383 | `U2_isCompact_of_triangulation` | U2 |
| 387 | `U2_triangulation_empty` | U2 |
| 391 | `U2_triangulation_triangle` | U2 |
| 395 | `U2_triangulation_square` | U2 |
| 399 | `U2_isPositivePLOn_of_refines` | U2 |
| 404 | `U2_refine_fan` | U2 |
| 412 | `U2_refine_edge_split` | U2 |
| 422 | `U2_exists_ball_disjoint_faces` | U2 |
| 427 | `U2_local_structure` | U2 |
| 432 | `U2_edgeSeg_subset_frontier` | U2 |
| 439 | `U2_interior_face_subset_interior` | U2 |
| 444 | `U2_openSegment_subset_interior_of_two_faces` | U2 |
| 450 | `U2_frontier_eq_iUnion_boundary_edges` | U2 |
| 456 | `U2_pushforward` | U2 |
| 463 | `U2_inverse_isPositivePLOn` | U2 |
| 470 | `U2_isHomeoOnto_of_isPositivePLOn` | U2 |
| 475 | `U2_continuousOn_of_isPositivePLOn` | U2 |
| 491 | `U3_refine_along_lines` | U3 |
| 499 | `U3_refine_into` | U3 |
| 504 | `U3_common_refinement` | U3 |
| 510 | `U3_isPositivePLOn_comp` | U3 |
| 517 | `U3_isPositivePLSphereMap_comp` | U3 |
| 524 | `U3_isPositivePLToPlane_comp` | U3 |
| 531 | `U3_isPositivePLToPlane_comp_plane` | U3 |
| 538 | `U3_isPositivePLFromPlane_inv` | U3 |
| 551 | `U4_polygonImage_isCompact` | U4 |
| 555 | `U4_range_traversal` | U4 |
| 559 | `U4_exists_insideModel` | U4 |
| 563 | `U4_polygonImage_subset_interior_square` | U4 |
| 568 | `U4_three_le_of_embedded` | U4 |
| 572 | `U4_triangle_base` | U4 |
| 579 | `U4_exists_ear` | U4 |
| 587 | `U4_polygonImage_ear` | U4 |
| 595 | `U4_exists_triangulation` | U4 |
| 609 | `U5_exists_ear_homeo` | U5 |
| 627 | `U5_pushforward_edges` | U5 |
| 663 | `U6_exists_ambientParam` | U6 |
| 668 | `U6_compl_frontier_triangle` | U6 |
| 676 | `U6_exteriorRegion_eq` | U6 |
| 682 | `U6_interiorRegion_eq` | U6 |
| 688 | `U6_interiorRegion_isConnected` | U6 |
| 693 | `U6_two_regions` | U6 |
| 699 | `U6_exterior` | U6 |
| 706 | `U6_two_regions_plane` | U6 |
| 713 | `U7_closure_interiorRegion_eq` | U7 |
| 719 | `U7_isPLDisc_image` | U7 |
| 724 | `U7_chartPart_cap_empty` | U7 |
| 729 | `U7_isPositivePLToPlane_inv` | U7 |
| 736 | `U7_pl_discs_inner` | U7 |
| 741 | `U7_isPLDisc_of_isPLDiscSphere` | U7 |
| 747 | `U7_isPLDisc_closure_interior` | U7 |
| 754 | `U8_capInvFun_capInvFun` | U8 |
| 759 | `U8_supNorm_capInvFun` | U8 |
| 765 | `U8_capChart_isHomeoOnto` | U8 |
| 770 | `U8_capInvFun_seam` | U8 |
| 777 | `U8_exists_exterior_fan` | U8 |
| 786 | `U8_closure_exteriorRegion_eq` | U8 |
| 793 | `U8_isPositivePLSphereMap_inv` | U8 |
| 802 | `U8_pl_discs_outer` | U8 |
| 826 | `U9_interiorOnLeft_consistent` | U9 |
| 832 | `U9_interiorOnLeft_iff_turn` | U9 |
| 839 | `U9_interiorOnLeft_iff_rotation` | U9 |
| 846 | `U9_traversalPositiveFor_iff_cyclicPos` | U9 |
| 858 | `U9_lift_preserves_cyclicPos` | U9 |
| 891 | `U10_fan_extension` | U10 |
| 902 | `U10_boundary_map_of_lift` | U10 |
| 919 | `U10_pl_extension` | U10 |
| 933 | `U11_frontier_eq_gauge_one` | U11 |
| 939 | `U11_radial_extension` | U11 |
| 946 | `U11_boundary_homeo_of_lift` | U11 |
| 958 | `U11_top_extension` | U11 |

## 3. Order of attack

Lanes in parallel first: **A** U1 → U2 → U3 (generic PL library, polygon-free); **B** U4 (needs U1's triangle
basics only: `U1_mem_carrier_iff_det`, `U1_frontier_triangle`); **C** U10's convex leaves `U10_fan_extension` and
U11's `U11_frontier_eq_gauge_one`, `U11_radial_extension` (polygon-free, against the `Link.IsDisc`/`Triangulation`
interface); **D** U0 (AUTHOR_NOTES ← PLAN_FINAL §5, this report).  Then sequentially U5 → U6 → U7 → U9 → U8 → U10/U11
(polygon-dependent leaves) → U12 (port to `work/lean/SM/GaussTwoDiscs*.lean`, `#print axioms lem_gauss_two_discs`).
First kernel-checked clause: 57a at `U6_two_regions`.

Working protocol for every unit file: copy `Skeleton_FINAL.lean` to `U<k>_work.lean`, close the unit's leaves in place
(never change a leaf statement another unit consumes; if a statement must change, record it in AUTHOR_NOTES and update
the skeleton + all unit files), run `python3 check_57_identity.py U<k>_work.lean`, typecheck, and report the remaining
`sorry` count.

## 4. Per-unit prompts (paste to the executor)

Common header for every prompt: "You work in
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912 (Lean 4 v4.34.0-rc2, Mathlib
pin; `source /workspace/envs/lean/env.sh` in every shell; never write under work/lean; never `lake build`; typecheck with
`cd work/lean && lake env lean ../drafts/twodiscs/<file>.lean`; never print an API key).  Write in SMALL pieces (each
Write/Edit under ~250 lines), typecheck after each piece, keep responses short.  Start from
work/drafts/twodiscs/Skeleton_FINAL.lean; do not alter the frozen blocks (run check_57_identity.py) and do not alter the
statement of any leaf outside your unit.  Read PLAN_FINAL.md §3.3 row for your unit and SKELETON_REPORT.md §5."

* **U1 (lane A, ~1300 lines).** Close the 21 `U1_*` leaves (lines 269-373).  Convex-hull API: `convexHull_insert`,
  `segment`, `Convex.interior`; `Triangle.carrier = convexHull ℝ (range T.v)`; positivity `T.pos`.  For
  `U1_compl_compact_convex_isConnected` use a far circle plus radial rays.  For `U1_exists_affine_of_triangle` solve the
  2×2 system with `det ≠ 0`.
* **U2 (lane A, ~1600).** Close the 18 `U2_*` leaves (383-475) using U1.  `Triangulation.inter` gives the face-pair
  intersections; `U2_frontier_eq_iUnion_boundary_edges` is the master lemma, the other frontier leaves are corollaries.
  `U2_isHomeoOnto_of_isPositivePLOn`: continuity by the pasting lemma `U1_continuousOn_iUnion_of_finite`, then
  `IsCompact.isHomeomorph`-style (compact-to-Hausdorff injective).
* **U3 (lane A, ~2600).** Close the 8 `U3_*` leaves (491-538).  `U3_refine_along_lines` is the engine (cells = face ∩
  half-planes, fan from the barycentre, cyclic order of the cell's vertices via `det`); `U3_refine_into` and
  `U3_common_refinement` follow with the three edge lines of each face; the chart-bookkeeping leaves need only refinement
  plus `U1_isPositiveAffineOn_comp`/`_mono`.
* **U4 (lane B, ~3800).** Close the 9 `U4_*` leaves (551-595).  `U4_exists_ear` (Meisters) is the hard one: supporting
  vertex with nonzero turn (`exists_supporting_vertex_turn_ne_zero`), ear/diagonal dichotomy by `U1_mem_carrier_iff_det`
  against all edges, `deleteVertex` embedded (case split remote/adjacent under the reindexing).  `U4_exists_triangulation`
  by induction on `n` from `U4_triangle_base` + `U4_exists_ear` + `U4_polygonImage_ear`.
* **U5 (sequential, ~2100).** Close `U5_exists_ear_homeo`, `U5_pushforward_edges` (609-627).  Choose `o` in the face at
  the diagonal, `b'` beyond the ear apex with the thin wedge outside `U'` (positive-distance leaf
  `U2_exists_ball_disjoint_faces`), `p = [o,b'] ∩ e`; four affine pieces via `U1_exists_affine_of_triangle`, glued by
  `U1_continuousOn_iUnion_of_finite`, homeomorphism by `U2_isHomeoOnto_of_isPositivePLOn` + identity outside.
* **U6 (sequential, ~1500).** Close the 8 `U6_*` leaves (663-706).  `U6_exists_ambientParam` by induction along the ear
  sequence composing the U5 homeomorphisms (refine `KT` by `U2_refine_fan`/`U2_refine_edge_split` at each step, so
  `plT` holds).  57a: `(sphereCircle P)ᶜ` = image of `interior T₀ ∪ T₀ᶜ` under `Homeomorph.onePointCongr A.H` with
  `∞` added to the second piece; two disjoint nonempty open connected sets ⇒ `Nat.card (ConnectedComponents _) = 2`.
* **U7 (sequential, ~1500).** Close the 7 `U7_*` leaves (713-747).  Witness for `U7_pl_discs_inner`: `D = T₀.carrier`,
  `f = A.H.symm ∘ planeOf`, plane chart triangulation = pushforward `U2_inverse_isPositivePLOn` of `A.KT`, cap chart
  `U7_chartPart_cap_empty` + `U2_triangulation_empty`; boundary clause from `A.boundary`.
* **U8 (sequential, ~2600).** Close the 8 `U8_*` leaves (754-802).  Chart algebra first (754-770), then the 11-ray fan
  `U8_exists_exterior_fan` (rays from `o₀ ∈ int T₀` through the 3 vertices and the 4 corners of `Q_L`; on `∂Q_L`
  the map is `x ↦ (x₁/L, −x₂/L)` matching the cap identity), then `f = g ∘ OnePoint.map A.H.symm` via
  `U3_isPositivePLToPlane_comp`.
* **U9 (sequential, ~1300).** Close the 5 `U9_*` leaves (826-858).  Route: `InteriorOnLeft` ⟺ `det` sign of the
  adjacent face of `A.H '' KT`; consistency by the ear induction; at the supporting vertex `cb_embedded_rotation
  (hP.regular hn) hP |>.orientation`.  Then transport through `f` (positive affine on the face containing the three
  boundary points' preimages after refinement) to `CyclicPos`.
* **U10 (lane C then sequential, ~2600).** Close `U10_fan_extension` (convex, polygon-free: cone from `z` to `z'`, marks
  = the segment endpoints, positivity by `PreservesCyclicPos`), then `U10_boundary_map_of_lift` (marks = images of the
  `IsFinitePL` marks and the vertices; `ea_traversal_eq_on_Icc` for affinity), then `U10_pl_extension` =
  `g' ∘ Fan ∘ f` with `U7_pl_discs_inner`/`U8_pl_discs_outer` witnesses, `U3_isPositivePLFromPlane_inv`,
  `U3_isPositivePLToPlane_comp_plane`, `U3_isPositivePLSphereMap_comp`, `U1_isHomeoOnto_comp`.
* **U11 (lane C then sequential, ~1300).** Close `U11_frontier_eq_gauge_one`, `U11_radial_extension` (Mathlib `gauge`,
  `x ↦ gauge D x • β (x / gauge D x)`-style with `z, z'` translated to `0`), `U11_boundary_homeo_of_lift`
  (`Embedded.traversal_injective`, periodicity `traversal_add_nat`), then `U11_top_extension` using the 57b witnesses at
  `L` from `U4_exists_insideModel`.

## 5. Pitfalls

* `Link.IsDisc` lives in namespace `SM.Link` (LinkMoves.lean:100): write `Link.IsDisc D` inside `namespace SM`; its
  fields are `Convex ℝ U ∧ IsCompact U ∧ (interior U).Nonempty`.
* `OnePoint` coercions: `((x : Plane) : Sphere)` is `OnePoint.some`; `∞` is `OnePoint.infty` (needs `open OnePoint`,
  already open).  Pattern-match `| ∞ => … | (x : Plane) => …` as in `planeOf`.  `Homeomorph.onePointCongr` transports a
  plane homeomorphism; `OnePoint.map A.H.symm` is used in `U8_isPositivePLSphereMap_inv` (both exist under the pin:
  `OnePoint.map : (X → Y) → OnePoint X → OnePoint Y`, `Homeomorph.onePointCongr : X ≃ₜ Y → OnePoint X ≃ₜ OnePoint Y`).
* `Nat.card` of an infinite type is `0`, so `Nat.card (ConnectedComponents Ω) = 2` genuinely asserts finiteness: prove it
  via an explicit `Equiv` with `Fin 2` or `Nat.card_eq_two_iff`.
* `Triangulation` is set-based (FR-TD-13): faces with the same carrier and rotated vertices may both occur; state
  uniqueness as equality of carriers (as the skeleton does), never of `Triangle`s.
* `Fin 3` arithmetic `T.v (i + 1)`, `T.v (i + 2)` wraps modulo 3 (elaborates fine, used in `Triangle.edgeSeg`).
* `IsPositivePLToPlane` quantifies over BOTH charts; for the interior disc the cap part is `∅` (`U7_chartPart_cap_empty`)
  and `Triangulation ∅` is the empty face set (`U2_triangulation_empty`).
* `cb_embedded_rotation` needs `Regular P`: use `hP.regular hn`.  `deleteVertex` needs `[NeZero n]` on the smaller size
  and `P : LabelledTuple (n + 1)`.
* `traversalPositiveFor P s` is `(0 < rotationNumber P ↔ s = Side.inner)`; the two `IsPositiveBoundaryLift` cases
  (`same`/`opposite`) are decided by `cb_embedded_rotation.pm_one` on both polygons.
* Never edit the frozen blocks; `check_57_identity.py` fails on a single changed byte (tested).
