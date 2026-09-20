# Row 57 lem:gauss-two-discs — unit U6 report (W2_U6)

Written 2026-09-19 (wave 2) by the U6 prover.  File: `work/drafts/twodiscs/W2_U6.lean` (14 150 lines =
`W1_Assembled.lean` 13 815 + 280 lines of `u6h_` helpers placed immediately after the `AmbientParam` structure and
before `U6_exists_ambientParam` + the 8 leaf bodies + one optional interface helper after the last U6 leaf).
Scratch (private): `/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/w2u6/`
(`pfx/W2U6Prefix.lean` = `W1_Assembled.lean[1..10733]` + `end SM`, built once as an olean in 31 s; pieces `A.lean`
(sphere topology), `B.lean` (ear induction), `C.lean` (card-two lemma, plane split), `D.lean` (sphere split, region
identification), `E.lean` (the 8 leaf bodies), `F.lean` (optional helper), each compiled against the prefix in
20-35 s; `assemble.py`; `W2_U6_axioms.lean`; `full_compile.log`, `axioms.log`).

## 1. Checks

| check | result |
|---|---|
| `cd work/lean && lake env lean ../drafts/twodiscs/W2_U6.lean` | **0 errors**; `declaration uses sorry` warnings: 22 (= the 22 open leaves of U5/U7/U8/U9); the rest linter/deprecation warnings as in wave 1 plus 4 `unused variable` warnings on the frozen headers of `U6_exteriorRegion_eq` / `U6_interiorRegion_eq` (`hn`, `hP` are not needed there — the statements are frozen, so they stay) |
| `python3 check_57_identity.py W2_U6.lean` | `IDENTITY OK` (DEFS, BUNDLE, THM byte-identical) |
| `grep -c sorry` | 33 (`W1_Assembled.lean`) → **25** (`W2_U6.lean`): the 8 U6 `sorry` bodies removed; 22 open leaves + 3 docstring mentions remain |
| `#print axioms` (scratch copy `W2_U6_axioms.lean`, compiled with `lake env lean`, 0 errors) | see §3 |
| leaves | **8/8 closed**: `U6_exists_ambientParam`, `U6_compl_frontier_triangle`, `U6_exteriorRegion_eq`, `U6_interiorRegion_eq`, `U6_interiorRegion_isConnected`, `U6_two_regions`, `U6_exterior`, `U6_two_regions_plane` (statements, names, docstrings untouched; only the `  sorry` lines replaced) |
| imports | none added |

## 2. What is proved (the route of W1_ASSEMBLY_REPORT §5 U6)

**`U6_exists_ambientParam`** — the ear induction, `u6h_ambient_induction (m : ℕ)`: for every embedded
`P : LabelledTuple (m + 3)` inside `Q_L` there are `T₀`, `H`, `K`, `KT` with `pl`, `plT`, `fix`, `inside` and the
invariant **`H '' T₀.carrier = u4h_regionOf P`** (U4's canonical region).
* Base `m = 0`: `T₀` = the ear triangle of `u4h_ear_triangle P 1` (carrier `earHull P 1 = u4h_regionOf P` by
  `u4h_regionOf_triangle`; its `det ≠ 0` is `U4_triangle_base`), `H = Homeomorph.refl`, `K`/`KT` any triangulations
  (`U2_triangulation_square`, `U2_triangulation_triangle`), `pl`/`plT` by `u6h_isPositivePLOn_refl`, `inside` from
  `u4h_regionOf_spec`.
* Step: `u4h_exists_convex_ear` picks the ear `j` (`hdet`, vertex-empty, on the region's side);
  `u4h_strict_ear_of_vertex_empty` → `hstrict`, `u4h_ends_ne_of_det` → `hac`, `u4h_embedded_deleteVertex` →
  `Embedded (deleteVertex P j)`; the induction hypothesis parametrises `U' := u4h_regionOf (deleteVertex P j)`;
  `u4h_regionOf_ear` gives **`hcut`** (`earHull P j ∩ U' = segment`) and `u4h_regionOf P = U' ∪ earHull P j`;
  `u4h_U4_exists_triangulation (deleteVertex P j)` gives `K'`, `hU'`, and `hedge`/`hface` at the edge `-1`
  (`u4h_edgeSegment_deleteVertex_last`); `hear` is `u4h_earHull_inter_polygonImage_delete`.  Then the black box
  **`U5_exists_ear_homeo`** gives `h`, and `H' := H.trans h`: `fix` by both fixings; `H' '' T₀ = h '' U' = U' ∪ ear =
  u4h_regionOf P`; `pl`/`plT` via `U3_isPositivePLOn_comp` (`H '' square L ⊆ square L` from `u6h_image_square_subset`:
  a plane homeomorphism fixing everything of sup-norm `≥ L` maps `Q_L` into itself, by injectivity;
  `H '' T₀ ⊆ U'` from the invariant) — the refinement produced by `U3_isPositivePLOn_comp` replaces the plan's
  `Kin.Refines K' + U2_isPositivePLOn_of_refines` bookkeeping.
* `u6h_exists_ambient_aux` converts `3 ≤ n` to `n = m + 3`; the leaf adds `boundary` from `Homeomorph.image_frontier`
  + the invariant + `(u4h_regionOf_spec …).1`.

**The region identification, for an arbitrary `A : AmbientParam P L`** (only `A.H`, `A.T₀`, `A.boundary` are used, so
`U6_interiorRegion_eq`/`U6_exteriorRegion_eq` do not depend on U5):
* `u6h_compl_frontier_triangle` (= `U6_compl_frontier_triangle`): `(frontier T)ᶜ = int T ∪ Tᶜ` (T closed),
  `U1_interior_convex_isConnected`, `U1_compl_compact_convex_isConnected`.
* `u6h_plane_split H T hb`: `Cᶜ = H '' int T ∪ (H '' T)ᶜ`, both open, connected, disjoint, `H '' T` compact
  (`Homeomorph.image_frontier`, `Set.image_compl_eq H.bijective`).
* Sphere topology (`u6h_compl_image_coe`: `(coe '' K)ᶜ = coe '' Kᶜ ∪ {∞}`; `u6h_infty_mem_closure`: `∞` is in the
  closure of the coe-image of an unbounded set, via `OnePoint.hasBasis_nhds_infty`; `u6h_not_isBounded_compl`: the
  complement of a compact plane set is unbounded, `NormedSpace.unbounded_univ`; `u6h_isConnected_compl_image`:
  `(coe '' K)ᶜ` is connected when `Kᶜ` is, by `IsPreconnected.subset_closure`; `u6h_isOpen_compl_image` via
  `OnePoint.isClosed_image_coe`).
* `u6h_sphere_split H T hb`: `sphereComplement P = coe '' (H '' int T) ∪ (coe '' (H '' T))ᶜ`, both open, connected,
  disjoint, `∞` in the second.
* `u6h_exteriorRegion_eq'`: `exteriorRegion P = (coe '' (H '' T))ᶜ` — `connectedComponentIn` is squeezed between
  `IsPreconnected.subset_connectedComponentIn` and `IsPreconnected.subset_right_of_subset_union`;
  `u6h_interiorRegion_eq'`: `interiorRegion P = coe '' (H '' int T)` by `union_sdiff_right` + disjointness.
  The leaves `U6_exteriorRegion_eq` (after `u6h_compl_image_coe`, `image_compl_eq`) and `U6_interiorRegion_eq` follow.

**57a / 57e.**  `u6h_card_connectedComponents_two`: if `S = A ∪ B` with `A`, `B` open, connected, disjoint (hence
nonempty), then `Nat.card (ConnectedComponents S) = 2` — through `Nat.card_eq_two_iff` (the two witnesses are the
components of a point of `A` and of `B`; `≠` by `subset_right_of_subset_union`, `= univ` by
`IsPreconnected.subset_connectedComponent`; the preimages in the subtype are preconnected by
`Topology.IsInducing.subtypeVal.isPreconnected_image` + `Subtype.image_preimage_coe`).  Applied to the sphere split
(`U6_two_regions`) and to the plane split (`U6_two_regions_plane`).  `U6_interiorRegion_isConnected` and `U6_exterior`
read off the splits (`∞ ∈ exteriorRegion` = `∞ ∉ coe '' _`; bounded/unbounded from `H '' T₀` compact via
`u6h_coe_preimage_image`, `u6h_not_isBounded_compl`).  These five leaves obtain `A` from `U4_exists_insideModel` +
`U6_exists_ambientParam`.

**Optional (done):** `u6h_sphereCircle_subset_closure_regionOf hn P hP s : sphereCircle P ⊆ closure (regionOf P s)`,
placed after `U6_two_regions_plane`, from the two region identities alone (`frontier T₀ ⊆ closure (int T₀)` by
`Convex.closure_interior_eq_closure_of_nonempty_interior`; `frontier T₀ ⊆ closure T₀ᶜ` by `frontier_compl`).  U11 may
replace its `u11h_circle_subset_closure` (U7/U8-dependent) by it.

## 3. Axioms (scratch copy `W2_U6_axioms.lean`)

```
'SM.U6_exists_ambientParam' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'SM.U6_compl_frontier_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.U6_exteriorRegion_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.U6_interiorRegion_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.U6_interiorRegion_isConnected' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'SM.U6_two_regions' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'SM.U6_exterior' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'SM.U6_two_regions_plane' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'SM.u6h_sphereCircle_subset_closure_regionOf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'SM.lem_gauss_two_discs' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'SM.two_regions_plane' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` enters every U6 result only through the one use of the open wave-2 leaf `U5_exists_ear_homeo` in the induction step of `u6h_ambient_induction` (hence in `U6_exists_ambientParam` and in the five leaves that obtain an `AmbientParam` from it); `U6_compl_frontier_triangle`, `U6_exteriorRegion_eq`, `U6_interiorRegion_eq` are sorry-free.  No literature axiom, no `native_decide`, no unregistered axiom.  Full compile: 0 errors, 22 `declaration uses sorry` warnings (lines 10681, 10700 = U5; 11121-11266 = U7/U8/U9), 32 s wall.

## 4. Remaining `sorry` (none in U6)

No U6 leaf is open; no rule-3 (false statement) case arose — every U6 statement was provable as frozen.  The 22 open
leaves in the file belong to U5 (2), U7 (7), U8 (8), U9 (5), untouched.  U6's own results depend on `sorryAx` only
through `U5_exists_ear_homeo` (used once, in the induction step of `u6h_ambient_induction`); `U6_compl_frontier_triangle`,
`U6_exteriorRegion_eq`, `U6_interiorRegion_eq` and all `u6h_` helpers except `u6h_ambient_induction`,
`u6h_exists_ambient_aux`, `u6h_sphereCircle_subset_closure_regionOf` are sorry-free.

## 5. Method audit (reassessment discipline)

No lemma needed a second method.  The compile-fix loop had only these iterations: (i) `Homeomorph.coe_refl` /
`Homeomorph.coe_trans` do not fire on the `DFunLike` coercion of `Plane ≃ₜ Plane` — replaced by `rfl` equations
(`⇑(H.trans h) = ⇑h ∘ ⇑H := rfl`) or by `exact` (defeq); (ii) `Disjoint.image_of_injective` does not exist —
`(Set.disjoint_image_iff H.injective).mpr`; (iii) `ConnectedComponents.coe_eq_coe'` needs `mem_singleton_iff` first
in the `right` branch of `{x, y} = univ`; (iv) assembler bug (the last leaf body swallowed `end SM`), caught by the
full compile.  Deprecations avoided: `mem_diff → mem_sdiff`, `union_diff_right → union_sdiff_right`.
Design decisions taken up front: the induction invariant is `H '' T₀ = u4h_regionOf P` (the canonical region makes
`hcut` and the union identity available at every step, W1_U4_REPORT §4); the region identities are proved for an
arbitrary `AmbientParam` from `boundary` alone, so U7/U8/U9 can use them with any `A`; `Nat.card = 2` is proved via
`Nat.card_eq_two_iff` rather than an explicit `Equiv` with `Fin 2` (same content, less bookkeeping; the pitfall
"`Nat.card` of an infinite type is 0" is irrelevant once two distinct elements exhaust `univ`).

## 6. Black boxes consumed (by name, statements untouched)

* Wave-2, still `sorry`: **`U5_exists_ear_homeo`** (corrected form with `hcut`; consumed with `n := m + 3`,
  `U' := u4h_regionOf (deleteVertex P j)`, `K'` from `u4h_U4_exists_triangulation`).  `U5_pushforward_edges` is not
  needed by U6.
* Wave-1 closed leaves: `U1_triangle_isCompact`, `U1_triangle_convex`, `U1_triangle_interior_nonempty`,
  `U1_interior_convex_isConnected`, `U1_compl_compact_convex_isConnected`, `U2_triangulation_square`,
  `U2_triangulation_triangle`, `U3_isPositivePLOn_comp`, `U4_triangle_base`, `U4_exists_insideModel`.
* U4 helpers: `u4h_regionOf`, `u4h_regionOf_spec`, `u4h_regionOf_triangle`, `u4h_regionOf_ear`, `u4h_exists_convex_ear`,
  `u4h_U4_exists_triangulation`, `u4h_strict_ear_of_vertex_empty`, `u4h_ends_ne_of_det`, `u4h_embedded_deleteVertex`,
  `u4h_earHull_inter_polygonImage_delete`, `u4h_edgeSegment_deleteVertex_last`, `u4h_ear_triangle`,
  `u4h_polygonImage_subset_interior_square`.
* No new interface from another unit was needed (no `u6h_` Prop with `sorry`).

## 7. Notes for U7/U8/U9/U11

* `u6h_sphere_split A.H A.T₀ A.boundary` and `u6h_plane_split` give, in one `obtain`, the open/connected/disjoint
  decomposition in the sphere and in the plane; `u6h_exteriorRegion_eq'` gives `exteriorRegion P = (coe '' (A.H '' A.T₀.carrier))ᶜ`
  (the form U8 wants, without the `∪ {∞}`), `u6h_compl_image_coe` converts.
* `H '' T₀ = u4h_regionOf P` holds for the parametrisation *constructed* by `u6h_exists_ambient_aux` (not for an
  arbitrary `A`); U7's `closure (interiorRegion P) = coe '' (A.H '' A.T₀.carrier)` follows for any `A` from
  `U6_interiorRegion_eq` + `Homeomorph.image_closure` + `Convex.closure_interior_eq_closure_of_nonempty_interior`
  (the same two lines as in `u6h_sphereCircle_subset_closure_regionOf`).
* `u6h_image_square_subset` (a homeomorphism fixing `{L ≤ supNorm}` maps `Q_L` into itself) may be useful to U8.
