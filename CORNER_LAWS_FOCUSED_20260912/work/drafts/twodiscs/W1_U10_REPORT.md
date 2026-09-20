# Row 57 — unit U10 report (`W1_U10.lean`)

Written 2026-09-19 by the U10 executor.  File: `work/drafts/twodiscs/W1_U10.lean` (3 230 lines; the skeleton
`Skeleton_FINAL.lean` is 1 039).  Typecheck: `cd work/lean && lake env lean ../drafts/twodiscs/W1_U10.lean` →
**0 errors, 89 `sorry` warnings** (skeleton: 92; the three U10 leaves are closed).  `python3 check_57_identity.py
W1_U10.lean` → IDENTITY OK (frozen blocks byte-identical).  `grep -c sorry`: 95 → 92 (the count includes three
docstring mentions of the word; the warning count 92 → 89 is the real one).

## Closed leaves (all three U10 leaves)

| leaf | line (skeleton) | status |
|---|---|---|
| `U10_fan_extension` | 891 | closed |
| `U10_boundary_map_of_lift` | 902 | closed |
| `U10_pl_extension` | 919 | closed (the 57c output leaf consumed by `lem_gauss_two_discs`) |

`#print axioms` (scratch copy): each of the three depends on `[propext, sorryAx, Classical.choice, Quot.sound]`;
the `sorryAx` enters only through the consumed leaves of other units listed below (no `u10h_` declaration and no
U10 leaf contains a `sorry`; checked by scanning every `sorry` line against the enclosing declaration).

No statement, name or docstring of the skeleton was changed; no leaf was found false; no new cross-unit
intermediate had to be postulated (rule 2 not used, rule 3 not used).

## Black boxes consumed (other units' leaves, by name)

`U1_isHomeoOnto_comp`, `U1_isHomeoOnto_inv`, `U2_isHomeoOnto_of_isPositivePLOn`, `U3_isPositivePLFromPlane_inv`,
`U3_isPositivePLSphereMap_comp`, `U3_isPositivePLToPlane_comp_plane`, `U4_range_traversal`,
`U6_exists_ambientParam`, `U7_closure_interiorRegion_eq`, `U7_pl_discs_inner`, `U8_closure_exteriorRegion_eq`,
`U8_pl_discs_outer`, `U9_traversalPositiveFor_iff_cyclicPos`.

Not consumed: `U9_lift_preserves_cyclicPos` (see §3) and `U11_boundary_homeo_of_lift` (declared after U10 in the
file; the homeomorphism clause is proved directly, §2).

## 1. `U10_fan_extension` (convex model, polygon-free; sm-3:535-537) — helpers before the leaf, ~1 100 lines

Radial gauge library about an interior point `z` (`u10h_rg D z x := gauge (D − z) (x − z)`, via Mathlib
`gauge_lt_one_iff_mem_interior`, `gauge_le_one_iff_mem_closure`, `gauge_eq_one_iff_mem_frontier`, `gauge_eq_zero`,
`continuous_gauge`): frontier = level 1, `D` = sublevel ≤ 1, the ray point `u10h_ray`.
* A straight frontier piece is never seen edge-on from `z` (`u10h_det_ne_zero_of_segment`); the fan triangle
  `conv{z,a,b}` over a frontier piece with `det (a−z) (b−z) > 0` is exactly the closed sector cut off by `D`
  (`u10h_mem_fan_iff`), and a frontier point in the closed sector lies on the piece (`u10h_frontier_mem_segment`).
* Marks `V` = endpoints of the `IsFinitePLOnFrontier` segments; adjacent pair `u10h_Adj a b` = both marks,
  `det > 0`, `[a,b] ⊆ frontier`, no mark in the open piece.  Uniqueness of the successor/predecessor and the
  no-crossing lemma (`u10h_adj_eq_of_openSegment`) are pure `det` algebra plus the sector lemma.
* Every frontier point lies on a nondegenerate segment of the cover (`u10h_exists_nondeg`: frontier points are not
  isolated, via continuity of the radial projection) and hence in an adjacent piece contained in one cover segment
  (`u10h_cover_of_segment`, a finite "gap" lemma on the parameter line).
* `u10h_fan_triangulation`: the fan faces `z a b` over adjacent pairs form a `Triangulation D` (finite: injection
  into `V × V`; cover: ray argument; `inter`: case analysis on where the ray point meets the two pieces).
* The cone map `u10h_cone D z z' β x := z' + rg x • (β (ray x) − z')` is affine on each fan face
  (`u10h_cone_eq_on_fan`, linear part in `det` coordinates `u10h_linOfDet`), positive because
  `det (β a − z') (β b − z') > 0` — derived from `PreservesCyclicPos` with a third mark and the sector lemma on `D'`
  (`u10h_pos_of_preserves`); injective on `D` (radial coordinate preserved, `β` injective on the frontier), onto
  `D'`, equal to `β` on the frontier.  `IsHomeoOnto D D'` via `U2_isHomeoOnto_of_isPositivePLOn` + image equality.

## 2. `U10_boundary_map_of_lift` — helpers before the leaf, ~900 lines

`β w := f' ↑(traversal P' (φ x))` for a chosen `x` with `f ↑(traversal P x) = w` (junk elsewhere); the boundary
clause holds by periodicity (`u10h_traversal_add_int_mul`, `u10h_lift_shift_same/opp`) and injectivity of the
parametrisation modulo `n` (`u10h_param_eq_iff`, from `Embedded.traversal_injective` and `f` injective on the
closed region).  `sphereCircle P ⊆ closure (regionOf P s)` (needed for that injectivity, not among the leaf's
hypotheses) is derived in `u10h_circle_subset_closure` from `U6_exists_ambientParam` + `U7_closure_interiorRegion_eq`
/ `U8_closure_exteriorRegion_eq`.
* Homeomorphism (`u10h_boundary_homeo`): bijective (surjectivity of `φ` by IVT, `u10h_lift_surj`), continuous by
  closed preimages (preimage of a closed set = image of a compact parameter set under the continuous
  parametrisation), then `Continuous.homeoOfEquivCompactToT2`.
* `PreservesCyclicPos` (`u10h_preservesCyclicPos`): parameters reduced to `[0,n)`, six orderings, each handled by
  `U9_traversalPositiveFor_iff_cyclicPos` on both sides together with totality of the cyclic order on a convex
  frontier (`u10h_cyclicPos_total`, proved from the gauge library: antipodal pairs handled by
  `u10h_det_prod_pos`), antisymmetry and rotation invariance.
* `IsFinitePLOnFrontier` (`u10h_finitePL`): breakpoints on the parameter line `[0,n]` = edge/face pieces of the
  plane-chart triangulation of `f` (`u10h_J`, compact convex parameter intervals), the `IsFinitePL` marks, and the
  pull-backs through `φ` of the edge/face pieces of `f'` (`u10h_J'`, translates by `m·n'`, finitely many by
  monotonicity of `φ`); on each gap all three are affine (`u10h_subset_piece` midpoint argument), so `β` is affine
  on the image segment (`u10h_affineOn_of_param`), and the gap segments cover the frontier (`u10h_gap'`).

## 3. `U10_pl_extension` — ~40 lines

`F := g' ∘ Fan ∘ f` with the `IsPLDiscSphere` witnesses of `U7_pl_discs_inner`/`U8_pl_discs_outer`, `β z z'` from
`U10_boundary_map_of_lift`, `Fan` from `U10_fan_extension`, `g'` from `U3_isPositivePLFromPlane_inv`;
homeomorphism by `U1_isHomeoOnto_comp`/`_inv`, chart bookkeeping by `U3_isPositivePLToPlane_comp_plane` +
`U3_isPositivePLSphereMap_comp`, boundary clause from `U4_range_traversal` and the left-inverse property of `g'`.

Method note on `U9_lift_preserves_cyclicPos`: as stated it needs `CyclicPos z (f↑γx) (f↑γy) (f↑γw)` for increasing
`x<y<w`, which is false when the traversal runs clockwise (`¬traversalPositiveFor P s`), so it cannot yield
`PreservesCyclicPos` alone; the iff-leaf plus totality does.  The leaf statement was left untouched.

## 4. Reassessment discipline

No lemma needed two failed proof attempts; iterations were compile-fix rounds (renamed Mathlib lemmas, casts,
`simp only` for `smul` splitting).  Scratch files: `/workspace/scratch/claude-0/-workspace-repos-lean/
d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/u10/` (`Fan.lean` = polygon-free library with sorry'd U2 copy,
`W2.lean` = the committed unit file).

## 5. Remarks for U11/U12

`u10h_boundary_homeo` (+ `hβc`) proves exactly the content of `U11_boundary_homeo_of_lift` once `β` is built as in
§2; U11 can reuse it at the port.  The radial gauge library (`u10h_rg_*`, `u10h_ray_*`) gives
`U11_frontier_eq_gauge_one` directly (`u10h_rg_eq_one_iff`, `u10h_rg_le_one_iff` with `z = 0`).
