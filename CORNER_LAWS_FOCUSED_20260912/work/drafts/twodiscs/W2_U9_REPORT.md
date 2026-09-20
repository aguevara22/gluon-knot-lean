# Row 57 lem:gauss-two-discs — WAVE-2 UNIT U9 REPORT (`W2_U9.lean`)

Written 2026-09-19 by the wave-2 U9 executor.  Directory: `work/drafts/twodiscs/`.  Input: `W1_Assembled.lean`
(13 815 lines).  Output: **`W2_U9.lean`** (15 162 lines; +1 347 lines, one `u9h_` block of 98 declarations placed
immediately before the first U9 leaf, plus the five leaf bodies).  Scratch (private):
`/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/w2u9/`
(`pfx/W2U9Prefix.lean` = lines 1-10895 of `W1_Assembled.lean` + `end SM`, compiled once to an olean; pieces
`P1.lean … P14.lean` compiled against it; `assemble.py`; `W2_U9_axioms.lean`; `compile_full.log`, `compile_axioms.log`).

## 0. Result

| check | result |
|---|---|
| `cd work/lean && lake env lean ../drafts/twodiscs/W2_U9.lean` | **0 errors**; 25 `declaration uses sorry` warnings = the 25 open leaves of U5-U8 (lines 10681-10875, unchanged); no warning of any kind from the `u9h_` block; 51 s wall |
| `python3 check_57_identity.py W2_U9.lean` | `IDENTITY OK` (DEFS, BUNDLE, THM) |
| `grep -c sorry` | 33 (`W1_Assembled.lean`) → **28** (`W2_U9.lean`) = 25 open leaves + 3 docstring mentions; `grep -c '^  sorry'`: 30 → 25 |
| U9 leaves | **5/5 closed**: `U9_interiorOnLeft_consistent`, `U9_interiorOnLeft_iff_turn`, `U9_interiorOnLeft_iff_rotation`, `U9_traversalPositiveFor_iff_cyclicPos` (fixed shape, untouched), `U9_lift_preserves_cyclicPos` (proved **as stated** — it is true, not only vacuous; §2.6) |
| statements / docstrings | every leaf statement and docstring byte-identical to `W1_Assembled.lean`; only the five `  sorry` lines replaced; no other unit's leaf touched |
| `#print axioms` (scratch copy `W2_U9_axioms.lean`, 0 errors) | all five U9 leaves: `[propext, sorryAx, Classical.choice, Quot.sound]`.  `sorryAx` enters **only** through the two U6 black boxes `U6_exists_ambientParam` and `U6_interiorRegion_eq` (the only open leaves referenced by the block, §3); every other dependency is a wave-1 closed leaf that W1_ASSEMBLY_REPORT §3 lists as sorry-free, or the accepted library.  When U6 closes those two leaves the five U9 leaves become `[propext, Classical.choice, Quot.sound]` with no further change.  No new axiom, no `native_decide`. |
| `#print` left in the unit file | none |

## 1. The five leaves (bodies)

| leaf | body | helper |
|---|---|---|
| `U9_interiorOnLeft_consistent` | `exact u9h_U9_interiorOnLeft_consistent hn P hP i j` | both sides `↔ 0 < rotationNumber P` (`u9h_interiorOnLeft_iff_rot`) |
| `U9_interiorOnLeft_iff_turn` | `exact u9h_U9_interiorOnLeft_iff_turn hn P hP hs ht` | `u9h_interiorOnLeft_iff_rot` + `(cb_embedded_rotation hn P (hP.regular hn) hP).orientation N i hs` |
| `U9_interiorOnLeft_iff_rotation` | `exact u9h_interiorOnLeft_iff_rot hn hP i` | `InteriorOnLeft P i ↔ R.σ = 1` (`u9h_interiorOnLeft_iff_sigma`) and `R.σ = 1 ↔ 0 < rotationNumber P` (`u9h_sigma_eq_one_iff_rot`) for any `R : u4h_Region P` (`u4h_region_exists`) |
| `U9_traversalPositiveFor_iff_cyclicPos` | `exact u9h_U9_traversalPositiveFor_iff_cyclicPos hn P hP s hL hD hf hB hpl hz hxy hyw hwx` | dichotomy `u9h_cyclic_dichotomy` + local evaluation `u9h_local_eval` + `u9h_sideSign_eq_one_iff` |
| `U9_lift_preserves_cyclicPos` | `exact u9h_U9_lift_preserves_cyclicPos hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hz hz' hφ hxy hyw hwx h` | leaf 4 on both polygons + `IsPositiveBoundaryLift.same/opposite` + totality `u9h_cyclicPos_total` + `u9h_cyclicPos_rotate` |

## 2. Method (what is actually proved), by block of the `u9h_` prefix

**A. `det` algebra and `CyclicPos` basics** (`u9h_det_*`, `u9h_det_leftNormal_pos`, `u9h_parallel_of_det_eq_zero`,
`u9h_cyclicPos_rotate/antisymm/ne`, `u9h_cyclicPos_collinear`, `u9h_continuous_det`, `u9h_isOpen_cyclicPos`).
`u9h_cyclicPos_collinear`: for `s > 0`, `CyclicPos z a (a + s•v) (a + 2s•v)` holds when `0 < det (a - z) v` and fails
when `det (a - z) v < 0` — the local test of §F.  `u9h_isOpen_cyclicPos`: the predicate along three continuous maps
is an open condition (three `isOpen_lt`).

**B. A convex disc `D` and its frontier** (`hD : Link.IsDisc D`, `hz : z ∈ interior D`).  `u9h_ray_unique` (two
frontier points on one ray from `z` coincide; `Convex.openSegment_interior_closure_subset_interior`),
`u9h_antipodal`, `u9h_det_prod_pos`, **`u9h_cyclicPos_total`** (re-proved here because U10's `u10h_cyclicPos_total`
sits after the U9 leaves in the file), `u9h_convex_det_eq_zero`, **`u9h_supporting_line`** (a closed convex disc
containing the frontier segment `{a + s v | s ∈ [0, δ]}` lies in one closed half-plane of its line; proof: two
points strictly on opposite sides would put the midpoint in the interior of `D` via the two triangles they span —
`u4h_mem_hull3_iff_det`, `u1h_isOpen_det_pos`, `interior_maximal`), **`u9h_interior_off_line`** (`z` is not on that
line: otherwise a frontier point lies on an open segment from `z` into `D`).

**C. The canonical region and the two complementary regions** (consumes the U6 black boxes).
`u9h_interior_eq_of_frontier_eq`: two closed bounded plane sets `U, W` with `frontier U = frontier W`, `W` with
preconnected interior and preconnected complement, `U` with nonempty interior, have `interior U = interior W`
(the Jordan-type argument: `Wᶜ` is preconnected and meets `Uᶜ` far away, so `Wᶜ ⊆ Uᶜ`; `interior W` is
preconnected and meets `interior U`, so `interior W ⊆ interior U`; `IsPreconnected.subset_or_subset`).
`u9h_regionOf_eq_image hn P hP A : u4h_regionOf P = A.H '' A.T₀.carrier` for any `A : AmbientParam P L`
(`Homeomorph.image_frontier/interior/compl`, `A.boundary`, `U1_interior_convex_isConnected`,
`U1_compl_compact_convex_isConnected`, `u4h_regionOf_spec`, `u4h_U4_exists_triangulation`).  Hence
**`u9h_interiorRegion_eq : interiorRegion P = coe '' interior (u4h_regionOf P)`** (from `U6_exists_ambientParam`
with `U4_exists_insideModel`, and `U6_interiorRegion_eq`), `u9h_coe_mem_interiorRegion_iff`,
`u9h_exteriorRegion_eq : exteriorRegion P = coe '' (u4h_regionOf P)ᶜ ∪ {∞}` (set algebra from
`exteriorRegion = sphereComplement \ interiorRegion`, no U6 leaf), the plane traces
`u9h_trace_inner : coe ⁻¹' closure (regionOf P inner) = u4h_regionOf P`,
`u9h_trace_outer : coe ⁻¹' closure (regionOf P outer) = (interior (u4h_regionOf P))ᶜ`
(`IsEmbedding.closure_eq_preimage_closure_image` of `OnePoint.isOpenEmbedding_coe`), packaged as
`u9h_trace P s` / `u9h_coe_mem_closure_regionOf_iff`, and **`u9h_circle_subset_closure : sphereCircle P ⊆ closure
(regionOf P s)`** (U10 derived the same fact from U7/U8; this one needs only the two U6 leaves).

**D. The face of the region at an edge; local structure at an edge midpoint.**  `u9h_segment_eq_iff` (equal
segments have the same endpoints up to order), `u9h_range_v`, `u9h_carrier_eq_of_edgeSeg`,
**`u9h_edge_face R i`**: `∃ T ∈ R.K.faces, ∃ a, T.carrier = convexHull {P i, P (i+1), a} ∧ range T.v = {P i, P (i+1), a}
∧ 0 < R.σ * det (P (i+1) - P i) (a - P i)` (from `R.edge_face`, `R.side`).  `u9h_hull3_side` (the triangle lies
in the closed `σ`-half-plane of the edge; near the midpoint `m = ½(P i + P (i+1))` the open `σ`-half-plane is
interior; `u4h_interior_hull3`, `u4h_mem_hull3_iff_det`), **`u9h_local_face`** (near `m` the region is that face:
`U2_local_structure R.K`; a face `T'` through `m` meets `T` in `convexHull (range T.v ∩ range T'.v) ∋ m`, and
the affine functionals `det (a - P (i+1)) (· - P (i+1))`, `det (a - P i) (· - P i)` force both endpoints into
`range T'.v`, then `R.edge_unique`), **`u9h_region_local R i`** (closed half-plane / open half-plane interior),
`u9h_sideSign R : Side → ℝ` (`σ` inner, `-σ` outer), **`u9h_trace_local`** (the trace of the closed region `s` near
`m` lies in the closed `sideSign`-half-plane), **`u9h_interiorOnLeft_iff_sigma : InteriorOnLeft P i ↔ R.σ = 1`**
(with `det e (leftNormal e) = ‖e‖² > 0`).

**E. `σ` is the sign of the rotation number.**  `u9h_lexmin_supporting` (the lexmin vertex of `u4h_exists_lexmin`
is supporting for `N = (1, 0)`), `u9h_turn_pos_iff/neg_iff` (`principalAngle_sign (hP.regular hn i)`: the sign of
`principalTurn P i` is the sign of `det (edge P (i-1)) (edge P i)`), **`u9h_sigma_eq_one_iff_rot : R.σ = 1 ↔ 0 <
rotationNumber P`** (`u4h_region_lexmin_turn` + `cb_embedded_rotation … |>.orientation`),
`u9h_interiorOnLeft_iff_rot`, `u9h_sideSign_eq_one_iff : u9h_sideSign R s = 1 ↔ traversalPositiveFor P s`.

**F. Leaf 4.**  `u9h_F P f t := f (traversal P t)` is continuous (`u9h_F_continuous`, from the homeomorphism and
`u9h_circle_subset_closure`), lands in `frontier D` (`u9h_F_mem_frontier`), and separates parameters of one period
(`u9h_F_ne`, from `Embedded.traversal_injective` and `InjOn` of the homeomorphism).  **`u9h_cyclic_dichotomy`**:
for such a loop, either every increasing triple `x < y < w < x + n` is in positive cyclic order around `z` or none is
— the domain `u9h_Ω n` of increasing triples is convex hence preconnected, the two sets `{CyclicPos z (F x) (F y)
(F w)}` and `{CyclicPos z (F x) (F w) (F y)}` are open, disjoint (`u9h_cyclicPos_antisymm`) and cover it
(`u9h_cyclicPos_total`), so `IsPreconnected.subset_or_subset` decides.  **`u9h_local_eval`** evaluates one triple:
`γ(½), γ(½ + δ/2), γ(½ + δ)` on edge `0` (`u9h_traversal_half`, from `traversal_int_add`).  A face `T` of the
plane-chart triangulation `K` (`hpl false`) contains `{m + t e | t ∈ [0, δ]}` (`u9h_face_along`, via
`U2_local_structure`; the edge points are in `chartPart L false (closure (regionOf P s))` by
`u9h_edge_point_mem_chartPart`), `f ∘ coe = M · + b` on `T` with `det M > 0` (`u9h_affine_det_pos`,
`u1h_det_linear`), so the three image points are `a, a + (δ/2)•Me, a + δ•Me` and `u9h_cyclicPos_collinear` reduces
the question to the sign of `det (M e) (z - a)`.  `T` lies in the closed `sideSign`-half-plane of the edge
(`u9h_convex_local_halfplane` from `u9h_trace_local`), has a vertex `v` strictly inside it
(`u9h_exists_vertex_off_line`), and `det (M e) (f v - a) = det M · det e (v - m)` has the sign `sideSign`; the image
segment lies in `frontier D`, so by `u9h_supporting_line` all of `D` — in particular `z`, which is off the line by
`u9h_interior_off_line` — is on the same side as `f v`: `0 < sideSign · det (M e) (z - a)`.  Hence the triple is
positive iff `sideSign R s = 1` iff `traversalPositiveFor P s`, and the dichotomy transports this to the given
`x, y, w`.

**Leaf 5 (§2.6).**  `h` gives `traversalPositiveFor P s` by leaf 4.  Case `same`: `φ` is strictly monotone with
`φ (x + n) = φ x + n'`, so `φ x < φ y < φ w < φ x + n'` and leaf 4 for `P'` gives the conclusion.  Case `opposite`:
`φ` is strictly antitone with `φ (x + n) = φ x - n'`, so `φ w < φ y < φ x < φ w + n'`; leaf 4 for `P'` at
`(φ w, φ y, φ x)` says `¬ CyclicPos z' (F' φw) (F' φy) (F' φx)`; totality of the three distinct frontier points
leaves `CyclicPos z' (F' φw) (F' φx) (F' φy)`, and one rotation is the conclusion.  So the leaf is true as
stated and is not vacuous (the wave-1 note "vacuous in the clockwise case" only means that then `h` fails).

## 3. Black boxes consumed (other units' leaves, by name; statements untouched)

* **Open (wave 2, U6), `sorry` in this copy — the only source of `sorryAx` in the five U9 leaves:**
  `U6_exists_ambientParam` (to obtain `A : AmbientParam P L` for the `L` of `U4_exists_insideModel`) and
  `U6_interiorRegion_eq` (`interiorRegion P = coe '' (A.H '' interior A.T₀.carrier)`), both used exactly once, in
  `u9h_interiorRegion_eq`.  Nothing else of U6 (in particular not `U6_exteriorRegion_eq`, `U6_two_regions`,
  `U6_interiorRegion_isConnected`) and nothing of U5/U7/U8 is used.
* **Closed wave-1 leaves (sorry-free):** U1: `U1_triangle_convex`, `U1_triangle_isCompact`,
  `U1_triangle_interior_nonempty`, `U1_interior_convex_isConnected`, `U1_compl_compact_convex_isConnected`;
  U2: `U2_local_structure`, `U2_interior_face_subset_interior`; U4: `U4_range_traversal`, `U4_exists_insideModel`,
  `U4_polygonImage_subset_interior_square`.
* **Wave-1 helpers used** (all sorry-free): `u4h_Region` (fields `K, U, σ, σ_pm, side, edge_face, edge_unique,
  face_subset`), `u4h_region_exists`, `u4h_regionOf`, `u4h_regionOf_spec`, `u4h_region_U_eq_regionOf`,
  `u4h_U4_exists_triangulation`, `u4h_region_lexmin_turn`, `u4h_exists_lexmin`, `u4h_Lex`,
  `u4h_triangulation_closure_interior`, `u4h_carrier_subset`, `u4h_mem_hull3_iff_det`, `u4h_interior_hull3`,
  `u4h_edgeSegment_eq_segment`, `u1h_isOpen_det_pos`, `u1h_det_linear`.
* **Accepted library:** `cb_embedded_rotation` (`.orientation`), `Embedded.regular`, `Embedded.edge_ne_zero`,
  `Embedded.traversal_injective`, `continuous_traversal`, `traversal_int_add`, `principalAngle_sign`
  (SM/RegularPairs; `Regular P i : RegularPair (edge P (i-1)) (edge P i)`, `principalTurn` unfolds to
  `principalAngle`).  Mathlib: `geometric_hahn_banach_*` was **not** needed (the supporting line is proved by the
  two-triangle argument); `IsPreconnected.subset_or_subset`, `Convex.openSegment_*_subset_interior`,
  `Convex.add_smul_sub_mem`, `Homeomorph.image_frontier/interior/compl`, `Topology.IsEmbedding.closure_eq_preimage_closure_image`,
  `OnePoint.isOpenEmbedding_coe`, `closure_eq_interior_union_frontier`, `segment_eq_image'`,
  `convexHull_convexHull_union_left`, `convexHull_pair`, the `module` tactic (vector identities).
* No new interface was needed from another unit (no `u9h_` Prop left with `sorry`).

## 4. Remaining `sorry` (none in U9)

`W2_U9.lean` keeps exactly the 25 open leaves of U5-U8 as in `W1_Assembled.lean` (lines 10681-10875 unchanged; the
same 25 `declaration uses sorry` warnings, none from U9).  U5 2, U6 8, U7 7, U8 8; see W1_ASSEMBLY_REPORT §4.

## 5. Method audits (reassessment discipline)

No lemma needed a second attempt at the level of "method"; every compile error was local (a `linear_combination`
coefficient, a `set` abbreviation not folded into a later `have`, `rw [map_smul]` also hitting `M m` — fixed with the
explicit `M.map_add m (t • e)`, a deprecated name).  Three design decisions replaced the planned route and are
recorded so U12 can judge them:

1. **Connectedness dichotomy instead of an angle lift.**  The plan suggested transporting through one face containing
   the three preimages (after refinement).  For arbitrary `x < y < w` this needs a global "degree one" argument; I
   used instead that the truth of `CyclicPos z (F x) (F y) (F w)` is locally constant on the convex domain of
   increasing triples (open, complement open by totality, `IsPreconnected.subset_or_subset`), so one evaluation at a
   convenient collinear triple on edge `0` decides all.  No `Real.Angle`, no lift, no refinement of `K`.
2. **`u4h_regionOf P = A.H '' T₀` via the U6 black boxes** (§2.C) instead of proving directly that
   `coe '' (u4h_regionOf P)ᶜ ∪ {∞}` is connected (which would need "the region has no holes" — not among the `u4h_Region`
   invariants).  The identification costs one Jordan-type lemma (`u9h_interior_eq_of_frontier_eq`, 40 lines) and makes
   the two U6 leaves the only open dependencies.  U6 may want to reuse `u9h_regionOf_eq_image` / `u9h_interiorRegion_eq`
   (they are stated for any `A : AmbientParam P L`), and U7/U8 may use `u9h_trace_inner/outer` and
   `u9h_circle_subset_closure` — but note they depend on `U6_interiorRegion_eq`, so U6 must not prove that leaf from them.
3. **Endpoints of a segment** (`u9h_segment_eq_iff`): `T.edgeSeg k = edgeSegment P i` only says the two segments are
   equal; to know the face's vertex set I proved that equal segments have equal endpoint pairs (40 lines,
   `segment_eq_image'` + `smul_left_injective`).  With it, `u9h_edge_face` gives the face at edge `i` as
   `convexHull {P i, P (i+1), a}` with `range T.v = {P i, P (i+1), a}` and no `Fin 3` index bookkeeping downstream.

Vacuity note (W1_ASSEMBLY_REPORT §2.2): `U9_lift_preserves_cyclicPos` is proved as stated; it is true, its hypothesis
`h` simply forces `traversalPositiveFor P s`.  No replacement is proposed.

## 6. Notes and pitfalls met

* U10's helpers (`u10h_cyclicPos_total`, `u10h_coe_traversal_mem_circle`, `u10h_frontier_param`, `u10h_isHomeoOnto_injOn`,
  `u10h_continuousOn_of_isHomeoOnto`, …) are declared **after** the U9 leaves, so they cannot be used by U9 helpers;
  the needed ones are re-proved with the `u9h_` prefix (totality without the gauge library: `u9h_ray_unique` from
  `Convex.openSegment_interior_closure_subset_interior`).  U12 may dedupe (`u10h_*` ← `u9h_*`) when porting.
* `rw` sees through `set`-abbreviations (zeta-delta): `rw [map_smul]` rewrote `M m` with `m := (1/2) • (p + q)`.  Use
  the explicitly instantiated `M.map_add m (t • e)` / `M.map_smul t e`.  Likewise a `have` created after `set σ'`
  keeps the unfolded `u9h_sideSign R s` unless given the type `σ' = 1 ∨ σ' = -1` explicitly.
* `chartPart L false S` unfolds by `rfl` to `square L ∩ (fun x => (x : Sphere)) ⁻¹' S`; `show supNorm x ≤ L` and
  `show ((x : Plane) : Sphere) ∈ S` are enough, no equation lemma needed.
* Deprecations under the pin: `Set.mem_setOf_eq → Set.mem_ofPred_eq`, `Set.mem_diff → Set.mem_sdiff`,
  `Set.diff_diff_cancel_left → sdiff_sdiff_cancel_left`, `continuousOn_iff_continuous_restrict →
  continuousOn_iff_continuous_domRestrict`.  `principalTurn_sign` (SM/UniformRotation) is not imported; use
  `principalAngle_sign` from SM/RegularPairs.
* Development: the prefix olean (`pfx/W2U9Prefix.lean`, `lean --root=pfx -o …`, ~6 min once) and 14 chained pieces of
  50-180 lines each, ~20-40 s per compile; `assemble.py` splices them (stripping `import`/`namespace`/`open`/`variable`
  lines) before the first U9 leaf docstring and replaces the five `  sorry` lines.  Full file: 51 s.
