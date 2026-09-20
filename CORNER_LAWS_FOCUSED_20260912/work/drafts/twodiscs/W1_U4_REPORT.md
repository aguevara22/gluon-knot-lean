# Row 57 lem:gauss-two-discs — unit U4 report (W1_U4)

Written 2026-09-19 11:35 UTC / 7:35am ET by the U4 prover.  File: `work/drafts/twodiscs/W1_U4.lean`
(6 400 lines: `Skeleton_FINAL.lean` + ~5 900 lines of `u4h_`-prefixed helpers placed in one block
immediately before the first U4 leaf, + the leaf bodies).

## 1. Checks

* `cd work/lean && lake env lean ../drafts/twodiscs/W1_U4.lean` → **0 errors**, 84 `declaration uses sorry`
  warnings (the 92 skeleton leaves minus the 8 closed here), a handful of linter warnings.
* `python3 check_57_identity.py W1_U4.lean` → `IDENTITY OK` (DEFS, BUNDLE, THM blocks byte-identical).
* `grep -c sorry`: Skeleton_FINAL 95 → W1_U4 87 (8 leaf `sorry`s removed; the other lines are docstrings).
* `#print axioms` (scratch copy `.../scratchpad/u4/final/W1_U4_axioms.lean`): every closed leaf and every
  helper listed in §3 depends on `[propext, Classical.choice, Quot.sound]` only — **no `sorryAx`**: the unit
  consumes no U1/U2 leaf (the triangle toolkit it needed was re-proved inside the `u4h_` block).
* One import added (allowed): `Mathlib.Analysis.Convex.Join` (for `convexHull_insert`).

## 2. Leaves

Closed (bodies are one-liners calling the helper of the same content):

| leaf | proof |
|---|---|
| `U4_polygonImage_isCompact` | `u4h_polygonImage_isCompact` |
| `U4_range_traversal` | `u4h_range_traversal` |
| `U4_exists_insideModel` | `u4h_exists_insideModel` |
| `U4_polygonImage_subset_interior_square` | `u4h_polygonImage_subset_interior_square` |
| `U4_three_le_of_embedded` | `u4h_three_le_of_embedded` |
| `U4_triangle_base` | `u4h_U4_triangle_base` |
| `U4_exists_ear` | `u4h_U4_exists_ear` (convex vertex-empty ear from face counting, §3) |
| `U4_exists_triangulation` | `u4h_U4_exists_triangulation` (the canonical region `u4h_regionOf P`) |

**Open (rule 3): `U4_polygonImage_ear` is FALSE as stated** (no hypothesis on `P`, `j`).  Counterexample:
`P : LabelledTuple 5`, `P 0 = (0,0), P 1 = (2,0), P 2 = (2,2), P 3 = (0,3), P 4 = (1,-1)`, `j = 1`: the point
`(0.6, 0.6)` of `edgeSegment P 3` lies on the open diagonal `(P 0, P 2)` and on no ear edge, so it is in
`polygonImage P` but not in the right-hand side.  The leaf is consumed by nobody outside U4 (only the
skeleton's own U4 induction was meant to use it), so nothing downstream changes.  The true form is proved as
```
u4h_polygonImage_ear [NeZero n] {P : LabelledTuple (n+1)} (hP : Embedded P) {j}
  (hac : P (j-1) ≠ P (j+1)) (hstrict : earHull P j ∩ polygonImage P = edgeSegment P (j-1) ∪ edgeSegment P j) :
  polygonImage P = (polygonImage (deleteVertex P j) \ openSegment ℝ (P (j-1)) (P (j+1))) ∪
    edgeSegment P (j-1) ∪ edgeSegment P j
```
(the hypotheses hold for every ear produced by `U4_exists_ear`/`u4h_exists_convex_ear`).  Assembly change
needed: add `hP`, `hac`, `hstrict` to the leaf statement (or drop the leaf).

## 3. Method (and the reassessment audit)

The plan (§3.3/§3.4 of PLAN_FINAL, SKELETON_REPORT §4) asked for Meisters' two-ears induction first and an
ear-gluing induction for the triangulation.  Two method changes were made early, before any failed attempt
cost time:

1. **Ear-gluing needs an orientation certificate.**  Gluing the ear triangle `T_j` to the region `U'` of
   `deleteVertex P j` needs `T_j ∩ U' = diagonal`; for a *reflex* ear (a notch, which satisfies the
   skeleton's `hear`) the triangle lies inside `U'` and the identity fails.  So the induction was changed to a
   **split along a clean diagonal from the lexmin vertex** `v` (case E: `v` has a vertex-empty ear triangle,
   the diagonal is `(P (v-1), P (v+1))`; case S: otherwise the farthest invader `w` of the ear triangle gives a
   clean diagonal `(P v, P w)`, `u4h_exists_clean_invader`), gluing the regions of the two sub-polygons
   (`u4h_subPoly`, `u4h_subPoly_embedded`).  The two exclusions the glue needs ("a chain point is outside the
   other region") come from the convex-hull bound at the strict lexmin (case E) and from the **local lexmin
   lemma** `u4h_local_lexmin` (LL): near the lexmin vertex, every point outside the closed cone of the two
   incident edges is outside the region (proof: the outside is the union of two open half-planes meeting in
   an antipodal sector, hence connected, disjoint from the frontier, and contains a point left of the lexmin,
   which is outside the hull).  Corollaries: `u4h_region_lexmin_turn` (the side `σ` of any region is the
   turn sign at the lexmin) and `u4h_lexmin_ray_outside`.
2. **Ears by counting, not by Meisters' recursion.**  Every region triangulation carries
   `count : #face-carriers + 2 ≤ n`; with each of the `n` edges a face-edge of a unique carrier, two edges
   share a face, they are consecutive, and that face is the ear triangle `T_{i+1}`, which is vertex-empty
   (`u4h_vertex_mem_hull_iff`) and convex (`side`): `u4h_exists_ear_of_region`.  Vertex-empty ⇒ strict ear
   is the geometric **ear criterion** `u4h_strict_ear_of_vertex_empty` (segment against a triangle:
   `u4h_segment_inter_tri`, via `IsPreconnected` frontier crossings and affine parameters, no
   sup/compactness arguments).

The invariants (structure `u4h_Region P`): a `Triangulation U` with `frontier U = polygonImage P`, every
edge a face-edge (`edge_face`), unique face carrier per edge (`edge_unique`), `U ⊆ convexHull (range P)`,
`IsPreconnected (interior U)`, a side `σ = ±1` with every face at an edge on the `σ`-side, and the face count.
Main results: `u4h_region_exists` (strong induction), `u4h_region_unique` / `u4h_sigma_unique` (any two
regions coincide: common interior half-disc at the lexmin edge + interior connectedness), the canonical
`u4h_regionOf`, and `u4h_regionOf_ear`.  Glue: `u4h_glueTri` (two triangulations meeting exactly in a common
face-edge; sub-face lemma `u4h_hull_inter_edge`, endpoint lemma `u4h_segment_endpoints`).

No lemma took more than two attempts at the method level; the compile-fix loop was ordinary.

## 4. Interface for the sequential units (U5, U6, U9)

All in `W1_U4.lean`, namespace `SM`, axioms-clean:

* `u4h_regionOf [NeZero n] (P : LabelledTuple n) : Set Plane` — the canonical closed bounded region.
  `u4h_regionOf_spec (hn : 3 ≤ n) P hP : frontier (regionOf P) = polygonImage P ∧ IsCompact _ ∧
  _ ⊆ convexHull ℝ (range P) ∧ ∀ L, InsideModel L P → regionOf P ⊆ interior (square L)`;
  `u4h_U4_exists_triangulation hn P hP : ∃ K : Triangulation (regionOf P), …` (the four U4 clauses on
  the canonical set); `u4h_regionOf_triangle (P : LabelledTuple 3) hP : regionOf P = earHull P 1`;
  `u4h_region_U_eq_regionOf hn hP (R : u4h_Region P) : R.U = regionOf P`.
* Ears: `u4h_exists_convex_ear (hn : 2 ≤ n') {P : LabelledTuple (n'+2)} hP : ∃ j, det (P j - P (j-1))
  (P (j+1) - P (j-1)) ≠ 0 ∧ u4h_VertexEmpty P j ∧ ∀ R : u4h_Region P, 0 < R.σ * det …` and, for such a `j`,
  `u4h_regionOf_ear hn hP hdet hV hconv : earHull P j ∩ regionOf (deleteVertex P j) = segment ℝ (P (j-1))
  (P (j+1)) ∧ regionOf P = regionOf (deleteVertex P j) ∪ earHull P j` — the set identities U5/U6 need
  (`T_{k+1} ∩ U_k = e_{k+1}`, `U_{k+1} = U_k ∪ T_{k+1}`), consistent along the whole ear sequence because the
  region is canonical.  Also `u4h_strict_ear_of_vertex_empty`, `u4h_embedded_deleteVertex`,
  `u4h_earHull_inter_polygonImage_delete` (= the `hear` clause), `u4h_polygonImage_ear`.
* Orientation (U9): `u4h_Region.side` is exactly "interior on the left of every edge iff `σ = 1`" and
  `u4h_region_lexmin_turn` identifies `σ` with the turn sign at the lexicographically least vertex, which is
  supporting for `N = (1,0)` (`cb_embedded_rotation.orientation` then gives `σ = rotationNumber P`).

**Flag for U5 (not edited, another unit's leaf):** `U5_exists_ear_homeo` as stated is not provable: the
reflex-ear ("notch") configuration satisfies `hP, hP', hturn, hear, hU', hedge, hface` with `earHull P j ⊆
U'`, and then `frontier (U' ∪ earHull P j) = polygonImage (deleteVertex P j) ≠ polygonImage P`.  It needs
the extra hypothesis `earHull P j ∩ U' = segment ℝ (P (j-1)) (P (j+1))` (equivalently `P j ∉ U'`), which
U6 obtains from `u4h_regionOf_ear` with `U' := u4h_regionOf (deleteVertex P j)`.

## 5. Black boxes

None.  No U1/U2 leaf is consumed; the accepted library is used through `Embedded`, `Regular`,
`exists_supporting_vertex_turn_ne_zero`, `principalAngle_zero_iff_det_zero`, `scalar_of_det_zero`,
`deletionIndex_*`, `deleteVertex_*`, `adjacent_distinct_cases`, `edgePoint_zero/one`, `remote_symm`.

## 6. Notes / pitfalls met

* `subst` on `k = v` may eliminate `v`; use `rw` for index equalities.  `linear_combination` signs in
  `ZMod n` were the most frequent fix.  `push_neg` is deprecated (use `not_le.mp` / `simp only [not_or]`).
* Sizes: `deleteVertex P j` for `P : LabelledTuple (n'+2)` equals `u4h_subPoly P (j+1) n'`
  (`u4h_deleteVertex_eq_subPoly`); the split with `m = 2` produces `LabelledTuple (n'+2-2+1)`, which is
  definitionally `LabelledTuple (n'+1)` — `u4h_Region_transport` moves regions along such equalities.
* Development was done in 32 chained scratch modules (`scratchpad/u4/U4A.lean` … `U4Zg.lean`, compiled with
  `lean --root` and a `LEAN_PATH` prefix) and spliced with a script; the final file is the only deliverable.
