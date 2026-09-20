# Row 57 lem:gauss-two-discs — WAVE-1 ASSEMBLY REPORT (`W1_Assembled.lean`)

Written 2026-09-19 by the wave-1 assembler.  Directory: `work/drafts/twodiscs/`.  Inputs: `Skeleton_FINAL.lean`
(1 039 lines, 92 leaves) and the unit files `W1_U1, W1_U2, W1_U3, W1_U4, W1_U10, W1_U11` (+ `W1_*_REPORT.md`).
Output: **`W1_Assembled.lean`** (13 815 lines).  Scratch (private): `/workspace/scratch/claude-0/-workspace-repos-lean/
d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/asm/` (`verify_units.py`, `merge.py`, `clash_scan.py`,
`W1_Assembled_axioms.lean`, `compile_*.log`).

## 0. Result

| check | result |
|---|---|
| `cd work/lean && lake env lean ../drafts/twodiscs/W1_Assembled.lean` | **0 errors**, 30 `declaration uses sorry` warnings (= the 30 open wave-2 leaves), 40 linter/deprecation warnings (§7); 1 m 04 s wall |
| `python3 check_57_identity.py W1_Assembled.lean` | `IDENTITY OK` (DEFS, BUNDLE, THM byte-identical to `Statements_FINAL.lean`) |
| leaves | 92 declared (each exactly once); **62 closed** (60 by the units + 2 closed here under their corrected forms, §2.2); **30 open** (U5 2, U6 8, U7 7, U8 8, U9 5) |
| `grep -c sorry` | 95 (skeleton) → 33 (= 30 leaves + 3 docstring mentions) |
| `#print axioms` (scratch copy, all 62 closed leaves + row + 3 bridges) | 58 closed leaves: `[propext, Classical.choice, Quot.sound]`; 4 closed leaves (`U10_boundary_map_of_lift`, `U10_pl_extension`, `U11_boundary_homeo_of_lift`, `U11_top_extension`) and `lem_gauss_two_discs`, `two_regions_plane`, `isPLDisc_of_isPLDiscSphere`, `isPLDisc_closure_interior`: additionally `sorryAx`, entering only through the open wave-2 leaves (§3).  **No literature axiom, no `native_decide`, no unregistered axiom.** |
| corrected forms (rule 3) | 3 leaf statements changed: `U3_isPositivePLFromPlane_inv` (+`hL : 0 < L`), `U4_polygonImage_ear` (+`hP hac hstrict`), `U5_exists_ear_homeo` (+`hcut`); details §2.2 |
| clash scan vs work/lean | **1 clash**: `SM.polygonImage` (frozen, §1 of the statements) vs `SM.polygonImage (C : PolyComp)` in `work/lean/SM/Rounding.lean:140` — a registered module; U12 blocker, §6 |

## 1. Verification of the unit files (task step 1)

Method (`verify_units.py`): `difflib.SequenceMatcher` of each unit file against the skeleton, line-based, no junk
heuristic.  Every skeleton line removed or changed must be a `sorry` body of the unit's own leaves; every declaration in
inserted text must carry the unit's prefix (`u<k>h_`) or sit in a `u<k>h_`-prefixed namespace; scoping commands
(`section`/`variable`/`open`/`set_option`/`omit`/`include`) in inserted text are listed.  In addition
`check_57_identity.py` on each unit file: all six `IDENTITY OK`.

| unit | lines | skeleton lines removed | own leaves closed | new decls (all prefixed?) | imports added | scoping in inserted text |
|---|---|---|---|---|---|---|
| U1 | 1 493 | 30: 21 `sorry` + **9 leaf headers changed `:= by` → `:=`** (term-mode bodies; statement text unchanged: `U1_triangle_isCompact`, `_convex`, `_isDisc`, `U1_mem_carrier_iff_det`, `U1_interior_convex_isConnected`, `U1_isPositiveAffineOn_comp`, `_of_det`, `U1_continuousOn_iUnion_of_finite`, `U1_isHomeoOnto_of_homeomorph`) | 21/21 | 33 `u1h_` (32 thm + 4 def incl. leaves re-listed) — yes | `Mathlib.Analysis.Normed.Module.Connected`, `Mathlib.Analysis.LocallyConvex.Separation`, `Mathlib.LinearAlgebra.Dimension.StrongRankCondition` | none |
| U2 | 2 629 | 17 `sorry` | 17/17 | 111 `u2h_` — yes; 3 `@[simp]` (`u2h_det_self`, `u2h_det_zero_right/left`) | `Mathlib.Topology.Algebra.Module.FiniteDimension`, `Mathlib.Analysis.Normed.Module.Connected` | `section split` / `section split2` with `variable … include hp`, both closed |
| U3 | 3 660 | 7 `sorry` | 7/8 (`U3_isPositivePLFromPlane_inv` left `sorry`, false as stated) | 158 `u3h_` (146 thm, 11 def, 1 structure) — yes; 1 `@[simp]` (`u3h_rot_v`) | `Mathlib.Analysis.Convex.Join`, `Mathlib.Analysis.LocallyConvex.Separation`, `Mathlib.Analysis.Convex.Extreme`, `Mathlib.Topology.Baire.CompleteMetrizable` | none |
| U4 | 6 416 | 8 `sorry` | 8/9 (`U4_polygonImage_ear` left `sorry`, false as stated) | 280 `u4h_` (266 thm, 12 def, 2 structures) — yes: the 19 short names `hne, inter, out1, out2, faces1, faces2, openDiag_interior, chain1_not_interior, chain2_not_interior, frontier_eq, int_conn, no_face2_chain1, no_face1_chain2, edge_face, edge_unique, sigma_eq, side, region', region` live inside `namespace u4h_SplitCtx` (full names `SM.u4h_SplitCtx.*`); 3 `@[simp]` (`u4h_mkTri_v0/1/2`, `rfl` lemmas) | `Mathlib.Analysis.Convex.Join` | 33 named sections `U4A_block … U4Zg_block`, all closed; `variable [NeZero n]` + two `omit [NeZero n] in` inside `U4H_block`; `namespace u4h_SplitCtx` (3×, with `variable … include C in`); one `set_option maxHeartbeats 800000 in`; one `open Classical in` |
| U10 | 3 230 | 3 `sorry` | 3/3 | 148 `u10h_` (133 thm, 15 def) — yes | none | none |
| U11 | 1 550 | 4 `sorry` | 4/4 | 31 `u11h_` (28 thm, 3 def) — yes | none | `open Classical in`, `open Classical Topology in` (scoped to one declaration each) |

Conclusion: no unit touched a frozen block, another unit's leaf statement, or a leaf docstring; every helper is
prefixed (namespace-aware); all scoping is closed or `in`-scoped.  The `@[simp]` attributes are on `det a a = 0`,
`det a 0 = 0`, `det 0 a = 0`, a rotation-`rfl` and three constructor-`rfl` lemmas; they did not disturb any other
unit's proofs in the merged file (0 errors).  Statement-level check of the merged file: exactly 16 non-`sorry`
skeleton lines differ, namely the 9 U1 headers above and the docstring/header lines of the three corrected leaves
(§2.2); everything else of the skeleton is verbatim.

Black boxes declared by the units (all by name, statements untouched — verified by the diff):
* U2 ← U1: `U1_affineOn_comp/_mono`, `U1_continuousOn_iUnion_of_finite`, `U1_exists_affine_of_triangle`,
  `U1_frontier_triangle`, `U1_isPositiveAffineOn_mono`, `U1_mem_carrier_iff_det`, `U1_triangle_convex/_isCompact`.
* U3 ← U1: `U1_triangle_isCompact/_convex/_interior_nonempty`, `U1_frontier_triangle`, `U1_mem_carrier_iff_det`,
  `U1_isPositiveAffineOn_mono/_comp`; ← U2: `U2_interior_face_subset_interior`, `U2_isPositivePLOn_of_refines`.
* U4: none.
* U10 ← `U1_isHomeoOnto_comp/_inv`, `U2_isHomeoOnto_of_isPositivePLOn`, `U3_isPositivePLFromPlane_inv`,
  `U3_isPositivePLSphereMap_comp`, `U3_isPositivePLToPlane_comp_plane`, `U4_range_traversal`, and the wave-2 leaves
  `U6_exists_ambientParam`, `U7_closure_interiorRegion_eq`, `U7_pl_discs_inner`, `U8_closure_exteriorRegion_eq`,
  `U8_pl_discs_outer`, `U9_traversalPositiveFor_iff_cyclicPos`.
* U11 ← `U4_exists_insideModel` and the wave-2 leaves `U7_pl_discs_inner`, `U8_pl_discs_outer`.

## 2. Merge (task step 2)

### 2.1 Method
`merge.py`: for each unit, the difflib opcodes against the skeleton are replayed onto the skeleton — `insert`
hunks (helpers) are placed before the skeleton line they precede in the unit file, `replace` hunks (leaf body, plus
any helpers the diff attached to it) replace the same skeleton range.  Assertions: no two units replace overlapping
skeleton ranges, no unit inserts inside another unit's replaced range; no anchor was shared by two units, so no
ordering choice was needed and **no renaming was necessary** (the prefixes `u1h_ … u11h_` are disjoint; the clash
scan of §6 confirms every name in the file is unique).  Imports = skeleton's 7 + the 7 distinct extras (U1 3, U2 1
new, U3 3 new, U4 0 new).  Order in the file is the skeleton's: frozen §1-§4, U1 (+454 lines), U2 (+1 590),
U3 (+2 621), U4 (+5 377), U5-U9 (open), U10 (+2 191), U11 (+511), frozen §5, row, bridges.  A `W1 assembly note`
block after the imports records the corrections.

Black boxes were connected automatically: a consumed leaf is the same declaration as the producing unit's closed
leaf (same name, same statement — the diff of §1 shows no statement drift), so e.g. all U2 and U3 leaves, which were
`sorryAx`-dependent in their unit files, are now sorry-free (§3).  The one black box whose shape did *not* match is
`U3_isPositivePLFromPlane_inv` (false as stated, consumed by `U10_pl_extension`); it is handled in §2.2.

### 2.2 Corrected forms applied (rule 3) — marked `W1 ASSEMBLY (rule 3)` in the docstrings
1. **`U3_isPositivePLFromPlane_inv`** — hypothesis `(hL : 0 < L)` added after `{L : ℝ}` (W1_U3_REPORT §3: for
   `L ≤ 0` both chart parts are empty, `IsPositivePLToPlane L S f` holds vacuously and the conclusion fails; explicit
   counterexample there).  Body: `u3h_isPositivePLFromPlane_inv hL hD hf hpl` — **closed**, sorry-free.  Only consumer:
   `U10_pl_extension`, patched at its one call site to
   `U3_isPositivePLFromPlane_inv (U4_polygonImage_subset_interior_square P' hL').2 hD' hf' hpl'` (the `0 < L'` comes
   from `InsideModel L' P'`).
2. **`U4_polygonImage_ear`** — hypotheses `(hP : Embedded P)`, `(hac : P (j - 1) ≠ P (j + 1))`,
   `(hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j - 1) ∪ edgeSegment P j)` added; conclusion unchanged
   (W1_U4_REPORT §2: counterexample `P = (0,0),(2,0),(2,2),(0,3),(1,-1)`, `j = 1`).  Body:
   `have h := u4h_polygonImage_ear hP hac hstrict; rwa [u4h_edgeSegment_prev, u4h_edgeSegment_eq_segment] at h` —
   **closed**, sorry-free.  Consumed by nobody.
3. **`U5_exists_ear_homeo`** (wave-2 leaf, flagged by U4 §4) — hypothesis
   `(hcut : earHull P j ∩ U' = segment ℝ (P (j - 1)) (P (j + 1)))` added after `hU'`.  Without it the leaf is false:
   for a reflex ear (notch) all skeleton hypotheses hold with `earHull P j ⊆ U'`, so `U' ∪ earHull P j = U'` and the
   conclusion `frontier (U' ∪ earHull P j) = polygonImage P` contradicts `frontier U' = polygonImage (deleteVertex P j)`
   (`P j` lies on one side only).  Still `sorry` (U5's job).  Consumed only by U6 (wave 2), which gets `hcut` from
   `u4h_regionOf_ear` with `U' := u4h_regionOf (deleteVertex P j)`.

Not changed (noted for wave 2): `U9_lift_preserves_cyclicPos` is true but vacuous when the traversal of `P` runs
clockwise (its hypothesis `h` is then unsatisfiable, W1_U10_REPORT §3); U10 did not consume it and closed
`PreservesCyclicPos` from `U9_traversalPositiveFor_iff_cyclicPos` + totality instead.  U9 may keep it (cheap) or
propose a replacement; no wave-1 code depends on it.

## 3. Axioms (task step 3)

Scratch copy `W1_Assembled_axioms.lean` = `W1_Assembled.lean` + `#print axioms` for the 62 closed leaves, the row
theorem and the 3 bridges (66 lines before `end SM`); compiled with `lake env lean`, 0 errors.

* `[propext, Classical.choice, Quot.sound]` (sorry-free): all 21 U1, all 17 U2, all 8 U3 (incl. the corrected
  `U3_isPositivePLFromPlane_inv`), all 9 U4 (incl. the corrected `U4_polygonImage_ear`), `U10_fan_extension`,
  `U11_frontier_eq_gauge_one`, `U11_radial_extension` — 58 leaves.
* `[propext, sorryAx, Classical.choice, Quot.sound]`: `U10_boundary_map_of_lift` (via `U6_exists_ambientParam`,
  `U7_closure_interiorRegion_eq`, `U8_closure_exteriorRegion_eq`, `U9_traversalPositiveFor_iff_cyclicPos`),
  `U10_pl_extension` (those + `U7_pl_discs_inner`, `U8_pl_discs_outer`), `U11_boundary_homeo_of_lift`,
  `U11_top_extension` (via `U7_pl_discs_inner`, `U8_pl_discs_outer`); `lem_gauss_two_discs` (via `U6_two_regions`,
  `U6_exterior`, `U7_pl_discs_inner`, `U8_pl_discs_outer` and the two above), `two_regions_plane`
  (`U6_two_regions_plane`), `isPLDisc_of_isPLDiscSphere` (`U7_isPLDisc_of_isPLDiscSphere`), `isPLDisc_closure_interior`
  (`U7_isPLDisc_closure_interior`).
* No other axiom appears anywhere (no literature axiom, no `Lean.ofReduceBool`).

## 4. Remaining `sorry` leaves (30), by unit, with the plan's size estimates (SKELETON_REPORT §4)

| unit | leaves (line in `W1_Assembled.lean`) | estimate |
|---|---|---|
| **U5** (2) | `U5_exists_ear_homeo` 10681 (corrected: `hcut` added), `U5_pushforward_edges` 10700 | ~2 100 lines |
| **U6** (8) | `U6_exists_ambientParam` 10736, `U6_compl_frontier_triangle` 10741, `U6_exteriorRegion_eq` 10749, `U6_interiorRegion_eq` 10755, `U6_interiorRegion_isConnected` 10761, `U6_two_regions` 10766, `U6_exterior` 10772, `U6_two_regions_plane` 10779 | ~1 500 |
| **U7** (7) | `U7_closure_interiorRegion_eq` 10786, `U7_isPLDisc_image` 10792, `U7_chartPart_cap_empty` 10797, `U7_isPositivePLToPlane_inv` 10802, `U7_pl_discs_inner` 10809, `U7_isPLDisc_of_isPLDiscSphere` 10814, `U7_isPLDisc_closure_interior` 10820 | ~1 500 |
| **U8** (8) | `U8_capInvFun_capInvFun` 10827, `U8_supNorm_capInvFun` 10832, `U8_capChart_isHomeoOnto` 10838, `U8_capInvFun_seam` 10843, `U8_exists_exterior_fan` 10850, `U8_closure_exteriorRegion_eq` 10859, `U8_isPositivePLSphereMap_inv` 10866, `U8_pl_discs_outer` 10875 | ~2 600 (chart algebra now mostly done in `u3h_`, see §5) |
| **U9** (5) | `U9_interiorOnLeft_consistent` 10899, `U9_interiorOnLeft_iff_turn` 10905, `U9_interiorOnLeft_iff_rotation` 10912, `U9_traversalPositiveFor_iff_cyclicPos` 10919, `U9_lift_preserves_cyclicPos` 10931 | ~1 300 |

(Line numbers: `grep -n "^theorem U[5-9]_" W1_Assembled.lean`.)  Output leaves still open on the row's critical
path: `U6_two_regions`, `U6_exterior`, `U7_pl_discs_inner`, `U8_pl_discs_outer` (direct fields of
`lem_gauss_two_discs`) and, feeding the closed U10/U11 leaves, `U6_exists_ambientParam`,
`U7_closure_interiorRegion_eq`, `U8_closure_exteriorRegion_eq`, `U9_traversalPositiveFor_iff_cyclicPos`.

## 5. Wave-2 specification (task step 4)

Common rules for every wave-2 unit: start from **`W1_Assembled.lean`** (not the skeleton); close only your own
`U<k>_` leaves; helpers `u<k>h_`-prefixed and placed before the leaf that uses them; never touch a frozen block
(`check_57_identity.py`), a leaf of another unit, or a leaf statement consumed by wave-1 code (list below) —
rule 3 (statement false) is reported, not silently edited; typecheck with `cd work/lean && lake env lean
../drafts/twodiscs/W2_U<k>.lean`; report black boxes by name.  The exact text of every open leaf (docstring +
statement, as it stands in `W1_Assembled.lean`) is reproduced in the Appendix.

**Statements that wave 1 already consumes and that therefore must not change** (their shape is fixed by closed
proofs): `U6_exists_ambientParam` (U10 `u10h_circle_subset_closure`), `U7_closure_interiorRegion_eq` and
`U8_closure_exteriorRegion_eq` (same), `U7_pl_discs_inner` and `U8_pl_discs_outer` (U10 `u10h_pl_discs`, U11
`u11h_pl_disc`, the row), `U9_traversalPositiveFor_iff_cyclicPos` (U10 `u10h_preservesCyclicPos`), plus the row's
direct fields `U6_two_regions`, `U6_exterior` and the bridges `U6_two_regions_plane`, `U7_isPLDisc_of_isPLDiscSphere`,
`U7_isPLDisc_closure_interior`.

### U5 — the ear-cut ambient homeomorphism (2 leaves, ~2 100 lines)
Leaves: `U5_exists_ear_homeo` (**corrected form**: hypothesis `hcut : earHull P j ∩ U' = segment ℝ (P (j - 1)) (P (j + 1))`
added, §2.2), `U5_pushforward_edges`.  Consumer: U6 only.
Wave-1 material to consume: `U1_exists_affine_of_triangle` (the four affine pieces), `U1_isPositiveAffineOn_of_det`,
`U1_continuousOn_iUnion_of_finite` (gluing), `U1_mem_carrier_iff_det` / `u1h_interior_triangle` (open-triangle
formula), `U2_exists_ball_disjoint_faces` (place `b'` beyond the apex with the thin wedge outside `U'`),
`U2_refine_fan`, `U2_refine_edge_split` (build `Kin ⊑ K'`), `U2_isHomeoOnto_of_isPositivePLOn`, `U2_pushforward`
/ `u2h_pushforward` (faces literally `T.map h _`; for `U5_pushforward_edges`), `u2h_affineOn_eq_of_vertices`
(two affine maps agreeing on the vertices agree on the face), `U2_frontier_eq_iUnion_boundary_edges` (the
`frontier (U' ∪ ear) = polygonImage P` clause), `U2_triangulation_square` + `U3_refine_into` /
`U3_common_refinement` (a triangulation `Kh` of `Q_L` on which `h` is PL: refine the square's triangulation into
the pieces' cells; `u3h_inter_of_family` is the general gluing criterion for hand-built triangulations,
`u3h_faces_separated` its separation input), `U4_polygonImage_subset_interior_square`, `u4h_edgeSegment_eq_segment`,
`u4h_edgeSegment_prev`, `u4h_edgeSegment_deleteVertex`, `u4h_edgeSegment_deleteVertex_last`
(`edgeSegment (deleteVertex P j) (-1) = segment (P (j-1)) (P (j+1))`), `u4h_strict_ear_of_vertex_empty`.
Route (PLAN_FINAL §3.1 / SKELETON_REPORT §4): `o` in the face of `K'` at the diagonal (from `hface`), `b'` beyond
`P j` in the thin wedge, `p = [o, b'] ∩ diagonal`; `h` = identity outside the quadrilateral `o, P (j-1), b', P (j+1)`,
affine on the four triangles; `hcut` makes `h '' U' = U' ∪ earHull P j`.

### U6 — 57a / 57e via the ambient parametrisation (8 leaves, ~1 500 lines)
Leaves: `U6_exists_ambientParam`, `U6_compl_frontier_triangle`, `U6_exteriorRegion_eq`, `U6_interiorRegion_eq`,
`U6_interiorRegion_isConnected`, `U6_two_regions`, `U6_exterior`, `U6_two_regions_plane` (all fixed-shape, see
above, except `U6_compl_frontier_triangle`, `U6_exteriorRegion_eq`, `U6_interiorRegion_eq`,
`U6_interiorRegion_isConnected`, which only U7/U8/U9 consume — coordinate any change with them).
Wave-1 material: **U4's canonical region** — `u4h_regionOf P` (10047), `u4h_regionOf_spec` (10587: frontier,
compactness, hull bound, `⊆ interior (square L)`), `u4h_U4_exists_triangulation` (10545: the four U4 clauses on
`u4h_regionOf P`), `u4h_regionOf_triangle` (10578: `regionOf P = earHull P 1` for a 3-gon), `u4h_exists_convex_ear`
(10316: an ear `j` with nonzero turn, vertex-empty, on the region's side), `u4h_regionOf_ear` (10345:
`earHull P j ∩ regionOf (deleteVertex P j) = segment` **= U5's `hcut`**, and `regionOf P = regionOf (deleteVertex P j)
∪ earHull P j`), `u4h_embedded_deleteVertex` (6516), `u4h_earHull_inter_polygonImage_delete` (6406, = U5's `hear`),
`u4h_strict_ear_of_vertex_empty` (6336), `u4h_Region` (7068) / `u4h_region_U_eq_regionOf` (10050),
`U4_triangle_base`, `U4_three_le_of_embedded`, `U4_polygonImage_subset_interior_square`, `U4_exists_insideModel`;
U5's two leaves (composition of the ear homeomorphisms; `Kin.Refines K'` + `U2_isPositivePLOn_of_refines`,
`U3_isPositivePLOn_comp` / `U3_common_refinement` to keep `pl`, `plT`); `U2_triangulation_triangle`,
`U2_triangulation_square`; for 57a/57e: `U1_compl_compact_convex_isConnected`, `U1_interior_convex_isConnected`,
`U1_frontier_triangle`, `U1_triangle_isCompact/_convex/_interior_nonempty`, `U1_isHomeoOnto_of_homeomorph`,
`U1_isHomeoOnto_coe`, `u1h_interior_triangle`, `u1h_isPreconnected_exterior`.
Route: induction along the ear sequence of `u4h_exists_convex_ear` (from `n` down to 3), `H = h_m ∘ ⋯ ∘ h_1`,
`T₀` the last 3-gon (`u4h_regionOf_triangle`); 57a: `(sphereCircle P)ᶜ` = coe-image of `A.H '' (interior T₀ ∪ T₀ᶜ)`
with `∞` added to the second piece; two disjoint nonempty open connected sets ⇒ `Nat.card … = 2` via an explicit
`Equiv` with `Fin 2` (pitfall: `Nat.card` of an infinite type is 0).  Note for U11: U11's
`u11h_circle_subset_closure` derives `sphereCircle P ⊆ closure (regionOf P s)` from U7/U8; if U6 proves it directly
(it follows from `U6_interiorRegion_eq`/`U6_exteriorRegion_eq`), `U11_boundary_homeo_of_lift` becomes independent
of U7/U8 — optional.

### U7 — 57b for the interior region (7 leaves, ~1 500 lines)
Leaves: `U7_closure_interiorRegion_eq`, `U7_isPLDisc_image`, `U7_chartPart_cap_empty`, `U7_isPositivePLToPlane_inv`,
`U7_pl_discs_inner`, `U7_isPLDisc_of_isPLDiscSphere`, `U7_isPLDisc_closure_interior`.
Wave-1 material: `U6_exists_ambientParam`, `U6_interiorRegion_eq`, `U6_exteriorRegion_eq` (wave 2);
`U2_inverse_isPositivePLOn` / `u2h_pushforward` (plane-chart triangulation of `H (T₀)` = pushforward of `A.KT`,
`H.symm` positive PL on it), `U2_triangulation_empty` (cap chart), `U1_triangle_isDisc`, `U1_frontier_triangle`,
`U1_isHomeoOnto_of_homeomorph`, `U1_isHomeoOnto_coe`, `U1_isHomeoOnto_comp/_inv/_restrict`,
`u1h_isHomeoOnto_of_inv` (builder from a continuous two-sided inverse), `U3_isPositivePLToPlane_comp_plane`,
`u3h_interior_square_subset` (4640), `u3h_chartInv_chart` (4539), `U4_polygonImage_subset_interior_square`.
Route (SKELETON_REPORT §4): witness `D = T₀.carrier`, `f = A.H.symm ∘ planeOf`; `closure (interiorRegion P) =
coe '' (H '' T₀)` from `U6_interiorRegion_eq` + `A.H` a homeomorphism; the cap chart part is empty because the
closed region lies in `coe '' interior (square L)` (`A.inside`, `A.fix`).

### U8 — 57b for the exterior region (8 leaves, ~2 600 lines; chart algebra largely available)
Leaves: `U8_capInvFun_capInvFun`, `U8_supNorm_capInvFun`, `U8_capChart_isHomeoOnto`, `U8_capInvFun_seam`,
`U8_exists_exterior_fan`, `U8_closure_exteriorRegion_eq`, `U8_isPositivePLSphereMap_inv`, `U8_pl_discs_outer`.
Wave-1 material: **chart algebra already proved by U3** — `u3h_capInvFun_capInvFun` (4526, for `L ≠ 0`; gives
`U8_capInvFun_capInvFun` at once), `u3h_supNorm_capInvFun` (4765, `L > 0`; gives `U8_supNorm_capInvFun`),
`u3h_chartInv_chart` / `u3h_chart_chartInv` (4539/4550), `u3h_sphere_cover` (4781: the two charts cover the sphere
for `L > 0`), `u3h_seam` (4804: the seam relation between the charts), `u3h_interior_square_subset`; for the fan:
`U1_exists_affine_of_triangle`, `U1_isPositiveAffineOn_of_det`, `u3h_inter_of_family` (gluing criterion for the
11-ray fan), `u3h_faces_separated`, `U3_refine_along_lines`, `U2_isHomeoOnto_of_isPositivePLOn`,
`U2_triangulation_square`, `U1_square_isDisc`, `U1_isHomeoOnto_*`, `u1h_isHomeoOnto_of_inv`; for the composite:
`U3_isPositivePLToPlane_comp` (sphere map then plane map), `U3_isPositivePLSphereMap_comp`, `U2_inverse_isPositivePLOn`,
`U6_exists_ambientParam`, `U6_exteriorRegion_eq`, `U6_interiorRegion_eq`; `OnePoint.map A.H.symm` (Mathlib, pin
checked by the skeleton).
Route (PLAN_FINAL §3.3): rays from `o₀ ∈ interior T₀` through the 3 vertices and the 4 corners of `Q_L`; on
`∂Q_L` the fan map is `x ↦ (x₁/L, −x₂/L)`, matching the cap identity `capInvFun` on the seam so the cap chart part
is the affine reflection; `U8_pl_discs_outer` with `f = g ∘ OnePoint.map A.H.symm`.

### U9 — orientation bookkeeping (5 leaves, ~1 300 lines)
Leaves: `U9_interiorOnLeft_consistent`, `U9_interiorOnLeft_iff_turn`, `U9_interiorOnLeft_iff_rotation`,
`U9_traversalPositiveFor_iff_cyclicPos` (fixed shape: U10 consumes it), `U9_lift_preserves_cyclicPos` (consumed by
nobody; vacuous in the clockwise case, §2.2 — keep, or propose a replacement under rule 3).
Wave-1 material: `u4h_Region.side` (7068: every face at edge `i` lies on the `σ`-side of the edge) and
`u4h_region_lexmin_turn` (7442: `σ` = sign of the turn at the lexicographically least vertex `v`, which is a
supporting vertex for `N = (1,0)`), `u4h_lexmin_ray_outside` (7530), `u4h_region_U_eq_regionOf`, `u4h_regionOf_spec`;
the accepted `cb_embedded_rotation (hP.regular hn) hP |>.orientation` and `.pm_one`; `U6_interiorRegion_eq` (to
identify `InteriorOnLeft` with membership of the left-normal points in `coe '' (A.H '' interior T₀)`, or directly
with `interior (u4h_regionOf P)` once U6 shows `interiorRegion P = coe '' interior (u4h_regionOf P)`);
`U1_mem_carrier_iff_det`, `u2h_mem_interior_of_det_pos` / `u2h_det_pos_of_mem_interior` (959/968), `U2_local_structure`;
for the `CyclicPos` leaf: `U3_refine_into` / `u3h_refine_map_into_dep` (refine the plane-chart triangulation of `f`
so the traversal points' preimages lie in one face), `U1_isPositiveAffineOn_mono`, `u3h_interior_map` (4911),
`u1h_det_linear` (650: `det (M u) (M v) = det M · det u v`), and U10's `u10h_cyclicPos_total` (12157: totality of the
cyclic order on a convex frontier), `u10h_rg_*` gauge library, `U4_range_traversal`, `u10h_coe_traversal_mem_circle`
(12093).
Route (SKELETON_REPORT §4): `InteriorOnLeft P i ⟺ σ = 1` via `u4h_Region.side`; consistency is then immediate;
at the lexmin vertex `u4h_region_lexmin_turn` + `cb_embedded_rotation.orientation` give `σ = rotationNumber P`;
transport through `f` positive-affine on a face containing the three boundary points to get `CyclicPos`.

### U12 — port to `work/lean/SM/GaussTwoDiscs*.lean` and registration
Inputs: the wave-2 assembly (all 92 leaves closed).  Tasks: (i) split the ~25 000-line file into modules that
respect the 200-declaration / build-time norms of work/lean (suggested: `SM/GaussTwoDiscsDefs` = frozen §1-§4 +
skeleton vocabulary; `SM/GaussTwoDiscsPL` = U1-U3; `SM/GaussTwoDiscsEars` = U4; `SM/GaussTwoDiscsAmbient` = U5-U9;
`SM/GaussTwoDiscsExtension` = U10-U11; `SM/GaussTwoDiscs` = §5 bundle, row, bridges) — the frozen blocks must
remain byte-identical *within one file each* or `check_57_identity.py` must be re-pointed; (ii) drop the `W1
ASSEMBLY` notes and the `u<k>h_` naming if the repo norms want it (renaming helpers is safe; leaf names are
checker-relevant only for the row `SM.lem_gauss_two_discs`); (iii) clean the 40 linter warnings (§7) if the repo
lints; (iv) `#print axioms SM.lem_gauss_two_discs` = `[propext, Classical.choice, Quot.sound]`; (v) register the row
(`lem:gauss-two-discs` has `module: ""` in `lean-declarations.json`) and run `python3 tools/check_lean.py work/lean`.
**Blocker to resolve first — §6**: the frozen `SM.polygonImage` collides with `SM.polygonImage (C : PolyComp)` of the
*registered* module `SM.Rounding`; `check_lean.py` imports every registered module into one program (line 117), so
the port cannot be registered until one side is renamed or namespaced.  Options for the architect (decision
needed; not made here): (a) rename the frozen definition (e.g. `polygonCircle`) — changes a frozen block, so
`Statements_FINAL.lean`, `check_57_identity.py`, the skeleton and every unit file must be updated together and
re-frozen; (b) put the row-57 development in a sub-namespace `SM.GaussTwoDiscs` (then the checker-enforced name of
the row theorem must be confirmed against the target-name table); (c) rename `SM.polygonImage` in `SM.Rounding.lean`
(a registered, reviewed module — its rows' hashes/reviews would need renewal).

## 6. Namespace-aware clash scan against work/lean (task step 5)

`clash_scan.py` parses every `.lean` under `work/lean` (excluding `.lake`; 23 892 declarations) and
`W1_Assembled.lean` (901 declarations) with a namespace/section stack (handles `namespace A.B`, `end`, `_root_`,
block comments) and compares full names.

* **1 exact clash: `SM.polygonImage`** — `W1_Assembled.lean:78` (frozen §1: `polygonImage (P : LabelledTuple n)`) vs
  `work/lean/SM/Rounding.lean:140` (`polygonImage (C : PolyComp) : Set Plane := ⋃ i : ZMod C.k, edgeSegment C.P i`).
  `SM.Rounding` is not in the import closure of `Supplemental.lean` (332 modules) and none of the three modules the
  skeleton imports (`SM.EmbeddedRotation`, `SM.LinkMoves`, `SM.DeletedTuple`) reaches it, which is why every unit
  file compiles; but `SM.Rounding` (and its importers `SM.CeRounding`, `SM.Curl`, `CV.Rounding`, `CV.Curl`) **is a
  registered module** in `lean-declarations.json`, and `tools/check_lean.py` builds one program importing all
  registered modules — importing it together with the future row-57 module would fail with a duplicate
  declaration.  Decision needed before U12 (§5, U12).
* No other exact clash: the 48 frozen/skeleton vocabulary names (`Sphere`, `Triangle`, `Triangulation`, `Side`,
  `square`, `supNorm`, `planeOf`, `IsPLDisc`, `AmbientParam`, `CyclicPos`, `leftNormal`, `earHull`, …) and all 761
  `u<k>h_`/`U<k>_` names are unused in work/lean.
* Same short name in a different namespace (harmless, listed for awareness): `SM.Triangle.map` vs `…map` in
  `SM/PolynomialBlock.lean:267`, `SM/LinkRecordExtras.lean:478` (other namespaces); `SM.u4h_SplitCtx.hne` /
  `.side` vs `SM.hne`-like names in `SM/FrontRealizeGeometry.lean:1058`, `SM/GermSides.lean:18` (different full
  names; no ambiguity inside `namespace SM` because the `u4h_SplitCtx` ones are only referred to with their prefix).
* Structure-generated names (`Triangle.v`, `Triangulation.faces`, `Side.inner`, `GaussTwoDiscsData.two_regions`,
  `AmbientParam.H`, …) cannot clash because their parents do not.

## 7. Warnings in the merged file (0 errors) — for U12's clean-up, none blocking

40 non-`sorry` warnings: deprecations under the pin (`Set.mem_setOf_eq` → `Set.mem_ofPred_eq` ×3, `Set.setOf_true`,
`dif_pos` → `dite_eq_left` ×6, `if_neg` → `ite_eq_right`, `continuousOn_iff_continuous_restrict` →
`…_domRestrict`), 5 "Try this" (`simpa`/`exact?`-style suggestions), 6 unused-variable (`hx`, `hn` ×2, `hk`, `hP`,
`hainc`) plus the **frozen unused hypothesis `hD'`** in `U10_boundary_map_of_lift` (12831) and
`U11_boundary_homeo_of_lift` (13691) — kept as printed, as in the units' reports, 12 unused-`simp`-argument, one
`<;>` style note, one unused-tactic note (9345).  All at lines inside `u<k>h_` helpers or wave-1 leaf bodies; the
line numbers are in `compile_main.log`.

## Appendix — exact text of the 30 open leaves (docstring + statement, from `W1_Assembled.lean`)

### `U5_exists_ear_homeo` (W1_Assembled.lean:10681)
```lean
/-- U5 (sm-3:437-443 realised ambiently, PLAN_FINAL §3.1): cutting an ear `j` of `P` is realised by
a positive PL homeomorphism `h` of the plane, the identity outside a compact subset of `int Q_L`,
carrying the region `U'` bounded by the cut polygon onto `U' ∪ ear` and the cut circle onto the
circle of `P`.

W1 ASSEMBLY (rule 3, flagged by U4): hypothesis `hcut : earHull P j ∩ U' = segment ℝ (P (j - 1)) (P (j + 1))`
added (equivalently `P j ∉ U'`).  Without it the statement is false: for a reflex ear (a notch) all
skeleton hypotheses hold with `earHull P j ⊆ U'`, so `U' ∪ earHull P j = U'` and the clause
`frontier (U' ∪ earHull P j) = polygonImage P` fails (`frontier U' = polygonImage (deleteVertex P j)`).
U6 obtains `hcut` from `u4h_regionOf_ear` with `U' := u4h_regionOf (deleteVertex P j)`
(W1_U4_REPORT.md §4). -/
theorem U5_exists_ear_homeo [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1)) (hP : Embedded P)
    (j : ZMod (n + 1)) (hP' : Embedded (deleteVertex P j))
    (hturn : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hear : earHull P j ∩ polygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)))
    (U' : Set Plane) (K' : Triangulation U') (hU' : frontier U' = polygonImage (deleteVertex P j))
    (hcut : earHull P j ∩ U' = segment ℝ (P (j - 1)) (P (j + 1)))
    (hedge : ∀ T ∈ K'.faces, ∀ T' ∈ K'.faces, segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T.carrier →
      segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T'.carrier → T.carrier = T'.carrier)
    (hface : ∃ T ∈ K'.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ (P (j - 1)) (P (j + 1)))
    {L : ℝ} (hL : InsideModel L P) (hU'L : U' ⊆ interior (square L)) :
    ∃ (h : Plane ≃ₜ Plane) (Kh : Triangulation (square L)) (Kin : Triangulation U'),
      IsPositivePLOn h Kh ∧ IsPositivePLOn h Kin ∧ Kin.Refines K' ∧
      (∀ x, L ≤ supNorm x → h x = x) ∧
      h '' U' = U' ∪ earHull P j ∧ h '' polygonImage (deleteVertex P j) = polygonImage P ∧
      frontier (U' ∪ earHull P j) = polygonImage P ∧ U' ∪ earHull P j ⊆ interior (square L) := by
```

### `U5_pushforward_edges` (W1_Assembled.lean:10700)
```lean
/-- U5: the ear-cut homeomorphism sends the faces of the refined triangulation `Kin` of `U'` to a
triangulation of `U' ∪ ear` in which every edge of `P` is an edge of exactly one face. -/
theorem U5_pushforward_edges [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (U' : Set Plane) (Kin : Triangulation U') (h : Plane ≃ₜ Plane) (hh : IsPositivePLOn h Kin)
    (hU : h '' U' = U' ∪ earHull P j) (hC : h '' polygonImage (deleteVertex P j) = polygonImage P)
    (hedge' : ∀ i, ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment (deleteVertex P j) i)
    (huniq' : ∀ i, ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces, edgeSegment (deleteVertex P j) i ⊆ T.carrier →
      edgeSegment (deleteVertex P j) i ⊆ T'.carrier → T.carrier = T'.carrier) :
    ∃ K : Triangulation (U' ∪ earHull P j),
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      ∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier := by
```

### `U6_exists_ambientParam` (W1_Assembled.lean:10736)
```lean
/-- U6 (sm-3:437-443, the ear induction assembled): every embedded polygon inside `Q_L` has an
ambient parametrisation. -/
theorem U6_exists_ambientParam [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) : Nonempty (AmbientParam P L) := by
```

### `U6_compl_frontier_triangle` (W1_Assembled.lean:10741)
```lean
/-- U6: the complement of the frontier of a triangle has exactly the two components `int T₀`, `T₀ᶜ`. -/
theorem U6_compl_frontier_triangle (T : Triangle) :
    (frontier T.carrier)ᶜ = interior T.carrier ∪ (T.carrier)ᶜ ∧
      IsConnected (interior T.carrier) ∧ IsConnected (T.carrier)ᶜ ∧
      Disjoint (interior T.carrier) (T.carrier)ᶜ := by
```

### `U6_exteriorRegion_eq` (W1_Assembled.lean:10749)
```lean
/-- U6 (sm-3:486-489 "the region of the point at infinity"): the exterior region is the image of
the complement of the base triangle together with `∞`. -/
theorem U6_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) {L : ℝ}
    (A : AmbientParam P L) :
    exteriorRegion P = ((↑) : Plane → Sphere) '' (A.H '' (A.T₀.carrier)ᶜ) ∪ {∞} := by
```

### `U6_interiorRegion_eq` (W1_Assembled.lean:10755)
```lean
/-- U6: the interior region is the image of the open base triangle. -/
theorem U6_interiorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) {L : ℝ}
    (A : AmbientParam P L) :
    interiorRegion P = ((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier) := by
```

### `U6_interiorRegion_isConnected` (W1_Assembled.lean:10761)
```lean
/-- U6: the interior region is open and connected in the sphere. -/
theorem U6_interiorRegion_isConnected [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsConnected (interiorRegion P) ∧ IsOpen (interiorRegion P) := by
```

### `U6_two_regions` (W1_Assembled.lean:10766)
```lean
/-- U6 (57a, sm-3:430-431 / 486-489): exactly two complementary regions in the sphere. -/
theorem U6_two_regions [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents (sphereComplement P)) = 2 := by
```

### `U6_exterior` (W1_Assembled.lean:10749)
```lean
/-- U6 (sm-3:486-489 "the region of the point at infinity"): the exterior region is the image of
the complement of the base triangle together with `∞`. -/
theorem U6_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) {L : ℝ}
    (A : AmbientParam P L) :
    exteriorRegion P = ((↑) : Plane → Sphere) '' (A.H '' (A.T₀.carrier)ᶜ) ∪ {∞} := by
```

### `U6_two_regions_plane` (W1_Assembled.lean:10779)
```lean
/-- U6 (bridge, plane form of 57a): the exterior region minus `∞` stays connected. -/
theorem U6_two_regions_plane [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents ((polygonImage P)ᶜ : Set Plane)) = 2 := by
```

### `U7_closure_interiorRegion_eq` (W1_Assembled.lean:10786)
```lean
/-- U7: the closed bounded region is `H (T₀)`. -/
theorem U7_closure_interiorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) :
    closure (interiorRegion P) = ((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier) := by
```

### `U7_isPLDisc_image` (W1_Assembled.lean:10792)
```lean
/-- U7 (sm-3:490-493, the interior disc): `H (T₀)` is a plane PL disc. -/
theorem U7_isPLDisc_image [NeZero n] (P : LabelledTuple n) {L : ℝ} (A : AmbientParam P L) :
    IsPLDisc (A.H '' A.T₀.carrier) := by
```

### `U7_chartPart_cap_empty` (W1_Assembled.lean:10797)
```lean
/-- U7: the cap chart sees nothing of the closed bounded region. -/
theorem U7_chartPart_cap_empty [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) : chartPart L true (closure (interiorRegion P)) = ∅ := by
```

### `U7_isPositivePLToPlane_inv` (W1_Assembled.lean:10802)
```lean
/-- U7: `planeOf ∘ H⁻¹` is positive PL to the plane on the closed bounded region. -/
theorem U7_isPositivePLToPlane_inv [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) (A : AmbientParam P L) :
    IsPositivePLToPlane L (closure (interiorRegion P)) (A.H.symm ∘ planeOf) := by
```

### `U7_pl_discs_inner` (W1_Assembled.lean:10809)
```lean
/-- U7 (57b interior, sm-3:431 / 490-493): the closure of the bounded region is a PL disc of the
sphere with boundary the circle. -/
theorem U7_pl_discs_inner [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) : IsPLDiscSphere L (closure (regionOf P Side.inner)) (sphereCircle P) := by
```

### `U7_isPLDisc_of_isPLDiscSphere` (W1_Assembled.lean:10814)
```lean
/-- U7 (bridge): a sphere PL disc lying in the plane chart is a plane PL disc. -/
theorem U7_isPLDisc_of_isPLDiscSphere {L : ℝ} {S B : Set Sphere} (hL : 0 < L)
    (hS : S ⊆ ((↑) : Plane → Sphere) '' square L) (h : IsPLDiscSphere L S B) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' S) := by
```

### `U7_isPLDisc_closure_interior` (W1_Assembled.lean:10820)
```lean
/-- U7 (bridge): the closed bounded region, as a plane set, is a plane PL disc. -/
theorem U7_isPLDisc_closure_interior [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' closure (interiorRegion P)) := by
```

### `U8_capInvFun_capInvFun` (W1_Assembled.lean:10827)
```lean
/-- U8 (chart algebra, PLAN_FINAL §4): the sup-norm inversion is an involution off `0`. -/
theorem U8_capInvFun_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    capInvFun L (capInvFun L y) = y := by
```

### `U8_supNorm_capInvFun` (W1_Assembled.lean:10832)
```lean
/-- U8: `‖capInvFun L y‖_∞ = L / ‖y‖_∞`. -/
theorem U8_supNorm_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    supNorm (capInvFun L y) = L / supNorm y := by
```

### `U8_capChart_isHomeoOnto` (W1_Assembled.lean:10838)
```lean
/-- U8 (sm-3:448-456 "the actual one-point-compactified exterior"): the cap chart is a homeomorphism
of `Q_1` onto the closed exterior of `Q_L` together with `∞`. -/
theorem U8_capChart_isHomeoOnto {L : ℝ} (hL : 0 < L) :
    IsHomeoOnto (square 1) (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) (capChart L) := by
```

### `U8_capInvFun_seam` (W1_Assembled.lean:10843)
```lean
/-- U8: on the seam `‖y‖_∞ = 1` the cap chart is the affine map `y ↦ L • (y₁, −y₂)`. -/
theorem U8_capInvFun_seam {L : ℝ} {y : Plane} (hy : supNorm y = 1) :
    capInvFun L y = L • (y.1, -y.2) := by
```

### `U8_exists_exterior_fan` (W1_Assembled.lean:10850)
```lean
/-- U8 (the 11-ray fan, PLAN_FINAL §3.3): the model exterior `Sphere \ int T₀` of a triangle inside
`int Q_L` is carried onto the square `Q_2` by a homeomorphism that is positive PL in the two model
charts and sends `∂T₀` onto `∂Q_2`. -/
theorem U8_exists_exterior_fan {L : ℝ} (hL : 0 < L) (T₀ : Triangle)
    (hT : T₀.carrier ⊆ interior (square L)) :
    ∃ g : Sphere → Plane,
      IsHomeoOnto (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ (square 2) g ∧
      IsPositivePLToPlane L (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ g ∧
      g '' (((↑) : Plane → Sphere) '' frontier T₀.carrier) = frontier (square 2) := by
```

### `U8_closure_exteriorRegion_eq` (W1_Assembled.lean:10859)
```lean
/-- U8: the closed exterior region is the sphere minus the open image triangle. -/
theorem U8_closure_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) :
    closure (exteriorRegion P) = (((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier))ᶜ := by
```

### `U8_isPositivePLSphereMap_inv` (W1_Assembled.lean:10866)
```lean
/-- U8: `H⁻¹` extended by the identity at `∞` is a positive PL sphere map (model `L` to model `L`)
on the closed exterior region. -/
theorem U8_isPositivePLSphereMap_inv [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) (A : AmbientParam P L) :
    IsPositivePLSphereMap L L (closure (exteriorRegion P)) (OnePoint.map A.H.symm) ∧
      IsHomeoOnto (closure (exteriorRegion P)) (((↑) : Plane → Sphere) '' interior A.T₀.carrier)ᶜ
        (OnePoint.map A.H.symm) := by
```

### `U8_pl_discs_outer` (W1_Assembled.lean:10875)
```lean
/-- U8 (57b exterior, sm-3:431 / 448-456 / 490-493): the closure of the exterior region is a PL disc
of the sphere with boundary the circle. -/
theorem U8_pl_discs_outer [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) : IsPLDiscSphere L (closure (regionOf P Side.outer)) (sphereCircle P) := by
```

### `U9_interiorOnLeft_consistent` (W1_Assembled.lean:10899)
```lean
/-- U9: "interior on the left of edge `i`" is the sign of the face of the ear triangulation adjacent
to that edge; it is the same for all edges (consistency along the ear induction). -/
theorem U9_interiorOnLeft_consistent [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (i j : ZMod n) : InteriorOnLeft P i ↔ InteriorOnLeft P j := by
```

### `U9_interiorOnLeft_iff_turn` (W1_Assembled.lean:10905)
```lean
/-- U9 (sm-3:4762-4764 read at a supporting vertex): at a supporting vertex with nonzero turn the
interior is on the left iff the turn is positive. -/
theorem U9_interiorOnLeft_iff_turn [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {N : Plane} {i : ZMod n} (hs : IsSupportingVertex P N i) (ht : principalTurn P i ≠ 0) :
    InteriorOnLeft P i ↔ 0 < principalTurn P i := by
```

### `U9_interiorOnLeft_iff_rotation` (W1_Assembled.lean:10912)
```lean
/-- U9 (with `cb_embedded_rotation.orientation`): the interior is on the left of the traversal iff
the rotation number is positive. -/
theorem U9_interiorOnLeft_iff_rotation [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (i : ZMod n) : InteriorOnLeft P i ↔ 0 < rotationNumber P := by
```

### `U9_traversalPositiveFor_iff_cyclicPos` (W1_Assembled.lean:10919)
```lean
/-- U9 (the convention of `traversalPositiveFor`, FR-TD-9): a positive PL parametrisation `f` of the
closed region `s` onto a convex model `D` carries the traversal, read around an interior point `z`,
to the counterclockwise cyclic order exactly when `traversalPositiveFor P s`. -/
theorem U9_traversalPositiveFor_iff_cyclicPos [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (s : Side) {L : ℝ} (hL : InsideModel L P) {D : Set Plane} {f : Sphere → Plane}
    (hD : Link.IsDisc D) (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hB : f '' sphereCircle P = frontier D) (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    {z : Plane} (hz : z ∈ interior D) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) :
    traversalPositiveFor P s ↔
      CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
        (f ((traversal P w : Plane) : Sphere)) := by
```

### `U9_lift_preserves_cyclicPos` (W1_Assembled.lean:10931)
```lean
/-- U9 (positivity of the boundary map, sm-3:431-434 "positive"): a positive boundary lift, read in
two positive parametrisations, preserves the counterclockwise cyclic order. -/
theorem U9_lift_preserves_cyclicPos [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {φ : ℝ → ℝ}
    (hφ : IsPositiveBoundaryLift P s P' s' φ) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n)
    (h : CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
      (f ((traversal P w : Plane) : Sphere))) :
    CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ y) : Plane) : Sphere))
      (f' ((traversal P' (φ w) : Plane) : Sphere)) := by
```
