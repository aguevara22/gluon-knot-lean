# U_X report — Unit X (double points of the rounded curve, the carried diagram, flatness, cover), cf:lem-rounding

File: `work/drafts/rounding/U_X.lean` (copy of `Skeleton_FINAL.lean`; section "Unit X" = `section doubles`).
Date: 2026-09-14. Check: `cd work/lean && lake env lean ../drafts/rounding/U_X.lean` → **0 errors, 0 non-sorry
warnings, 37 warnings `declaration uses sorry`** (= the 52 − 15 leaves of the other units P, A, G1, G2, G3, E; none of
them anchored in the Unit X region, lines 984–1707). `grep -c sorry`: **54 before → 39 after** (the 15 Unit X leaves;
the 2 remaining non-leaf hits are the prose mentions in the §8 header and the file header, as before).
`diff Skeleton_FINAL.lean U_X.lean`: the only removed lines are the fifteen `  sorry` bodies; no definition,
statement, name or docstring changed; nothing written under `work/lean`.

`#print axioms` (scratch copy): all 15 leaves `[propext, sorryAx, Classical.choice, Quot.sound]` — the `sorryAx`
comes only through the black boxes of the other units (every leaf uses at least `Λ_pos`, which rests on
`juncLen_pos` (A) and `three_mul_lt_edgeLength` (G1)). The self-contained helpers `X_regular_adjacent_meet`,
`X_iteratedDeriv_eq_zero_of_eqOn_open`, `X_visit_ext` are `[propext, Classical.choice, Quot.sound]`.

## Leaves proved (15 / 15)

| leaf | proof idea | black boxes used |
|---|---|---|
| `curveMap_junction_mem_disc` | `curveMap_on_junction` + `juncArc_mem_disc` at the profile argument `(t−a_j)Λ/ℓ_j ∈ [0,1]`; the centre `A₀ j + ε·dirOf(θu j) = q_j` by `dirOf_θu` | `curveMap_on_junction` (G2), `juncArc_mem_disc` (A), `dirOf_θu` (G1) |
| `curveMap_straight_notMem_discs` | the straight point is `q_j + r·δ_j/|δ_j|` with `ε < r < |δ_j| − ε` (strict, from `a(j+1) − b j = str_j/Λ`); case split on `incident i j`: `i = j` (distance `r > ε`), `i = j+1` (distance `|δ_j| − r > ε`), non-incident (`cornerDisc_disjoint_edge`, the point lies on `edgeSegment j`) | `curveMap_on_straight` (G2), `cornerDisc_disjoint_edge` (E), `three_mul_lt_edgeLength` (G1) |
| `range_curveMap_outside` | (→) reduce `t` to `fract t` by `curveMap_periodic`, then `X_cover`: a junction parameter lands in a disc (excluded), a straight one on `edgeSegment j`. (←) `p = edgePoint i s`; `p ∉ disc i, disc (i+1)` give `ε < s|δ_i| < |δ_i| − ε`, so `t := b i.val + (s|δ_i| − ε)/Λ` is on the straight part and `curveMap t = p` | `curveMap_on_straight`, `integral_tangentField_period` (via `curveMap_periodic`) (G2) |
| `τ_mem_straight` | `three_mul_lt_dist_crossing` at `q_j` and `q_{j+1}` read on `crossingPoint = edgePoint j c` gives `ε < c|δ_j| < |δ_j| − ε` (`X_crossingParam_bounds`); then `0 < (c|δ_j| − ε)/Λ < str_j/Λ = a(j+1) − b j` | `three_mul_lt_dist_crossing` (E), `three_mul_lt_edgeLength` (G1) |
| `τ_mem_Ico` | from `τ_mem_straight` and the monotonicity of `a` (`X_a_mono`: all summands `ℓ_i + str_i` positive), `a 0 = 0`, `a k = 1` | as above |
| `curveMap_τ` | `X_curveMap_straight` at `τ v`: `q_j + (ε + Λ(τ v − b j))·δ/|δ| = q_j + c|δ|·δ/|δ| = edgePoint j c = crossingPoint` | `curveMap_on_straight` (G2) |
| `deriv_curveMap_τ` | `deriv curveMap = Λ • dirOf (Θ t)`, `Θ = θu (j+1)` on the straight part, `dirOf (θu (j+1)) = u_{j+1} = v_j = |δ_j|⁻¹ • δ_j`; `r = Λ/|δ_j|` | `Θ_on_straight` (G2), `dirOf_θu` (G1) |
| `τ_injective` | labels differ ⇒ the open straight intervals are disjoint (`X_τ_lt_of_label_lt`); same label ⇒ same crossing parameter (cancel `Λ`, `ε`, `|δ|`) ⇒ same crossing point ⇒ same crossing (`Generic.crossingPoint_injective`) ⇒ same occurrence (`X_visit_ext`) | (Λ_pos only) |
| `doubles_curveMap` | `X_cover` on both parameters. junction–junction: same disc ⇒ `X_junction_injOn` (from `juncArc_injOn`), different discs ⇒ `cornerDisc_disjoint`. junction–straight: the straight point is in no disc. straight–straight: same edge ⇒ distances from `q_i` equal ⇒ `s = t`; adjacent edges ⇒ the common point is the shared vertex (`X_regular_adjacent_meet`), which is in its disc — contradiction; non-adjacent ⇒ `{⟨0,i⟩,⟨0,j⟩}` is a crossing `x` of `single C` (`isCrossing_pair`), the point is `crossingPoint x` (`Generic.common_point_unique`), `v := ⟨x, ⟨0,i⟩⟩`, `twin v` has strand `⟨0,j⟩` (`eq_other_of_mem_of_ne`), and `edgePoint_injective` identifies the crossing parameters with the straight-part parameters, whence `s = τ v`, `t = τ (twin v)` | `juncArc_injOn` (A), `cornerDisc_disjoint`, `cornerDisc_disjoint_edge` (E), `curveMap_on_junction/straight` (G2) |
| `transverse_τ` | velocities `r • δ_v`, `r' • δ_{twin v}` (`deriv_curveMap_τ`), `det` bilinear (`X_det_smul_smul`), `D.generic.transverse` with `not_adjacent_other`, `seg_inter_other_nonempty` | as `deriv_curveMap_τ` |
| `order_τ` | `X_τ_lt_iff : τ v < τ w ↔ visitCoord v < visitCoord w` (trichotomy on the edge labels; same label: cancel `b j`, `Λ`, `ε`, `|δ|`; `visitCoord v = label.val + crossingParam` is `rfl`); then `unfold cycBetween; rw` the three `<` | as `τ_mem_straight` |
| `sign_τ` | `det (r•u) (r'•w) = (rr') det u w`, `sign_mul`, `sign_pos`; `D.toDiagram.sign x` is definitionally `sign (det (edge (label (overVisit x))) (edge (label (underVisit x))))` (closed by `rfl`) | as `deriv_curveMap_τ` |
| `cover` | `X_cover`: `m := Nat.find (∃ n, t < a n)` (witness `k`, `a k = 1`); `m ≠ 0` since `a 0 = 0 ≤ t`; `j := m − 1 < k`, `a j ≤ t < a (j+1)`, split at `b j` | `a_last` (Λ_pos) |
| `iteratedDeriv_curveMap_a` | `iteratedDeriv (n+1) f = iteratedDeriv n (deriv f)`; `deriv curveMap` is `C^∞` (`contDiff_infty_iff_deriv`) and constant `= Λ • dirOf (θu (i+1))` on the open straight interval `(b i, a (i+1))` before `a (i+1)`; for `j = 0` on `(b (k−1) − 1, 0)` via `tangentField_periodic`; `X_iteratedDeriv_eq_zero_of_eqOn_open` at the closure point | `Θ_smooth` (via `curveMap_smooth`), `Θ_on_straight` (G2) |
| `iteratedDeriv_curveMap_b` | same on `(b j, a (j+1))` at its left end | same |

Leaves left: none.

## Helpers added (41 `theorem`s, all prefixed `X_`, inside `section doubles`, each immediately before the leaf that first
uses it; those not needing `h : Admissible C D ε` are declared with `omit h in`)

Before `curveMap_junction_mem_disc` (vectors, subdivision, straight parts, junctions):
`X_smul_normalize` (`|v| • normalize v = v`), `X_det_smul_smul`, `X_eucDist_add_smul_normalize`
(`eucDist (p + r • normalize v) p = |r|`), `X_eucDist_self`, `X_edgePoint_eq_add_smul_normalize`
(`edgePoint i (r/|δ_i|) = q_i + r • normalize δ_i`), `X_edge_ne_zero` (`Regular` ⇒ edges nonzero), `X_P_succ`
(`q_{i+1} = q_i + δ_i`), `X_eucDist_edgePoint` (distances `s|δ|`, `(1−s)|δ|` to the two ends), `X_A0_add_smul_dirOf`
(`A₀ j + ε • dirOf (θu j) = q_j`), `X_a_succ_sub_b` (`a (j+1) − b j = str_j/Λ`), `X_str_pos` (for every `j : ℕ`),
`X_a_mono`, `X_a_nonneg`, `X_a_le_one`, `X_curveMap_straight` (`q_j + (ε + Λ(t − b j)) • normalize δ_j`),
`X_straight_dist_bounds`, `X_straight_dist_bounds_strict`, `X_curveMap_straight_mem_edgeSegment`,
`X_eucDist_straight`, `X_junction_param_mem`, `X_junction_injOn` (the skeleton's `junction_embedded` argument as a
lemma).
Before `range_curveMap_outside`: `X_cover` (= the leaf `cover`, needed earlier in the file; `cover` is now `exact X_cover h ht`).
Before `τ_mem_straight`: `X_crossingPoint_eq`, `X_visitCoord_eq` (`rfl`), `X_label_val_lt`, `X_label_cast`,
`X_crossingParam_bounds`.
Before `τ_injective`: `X_visit_ext` (same crossing + same label ⇒ same occurrence), `X_τ_lt_of_label_lt`, `X_τ_eq_of_label_eq`.
Before `doubles_curveMap`: `X_regular_adjacent_meet`, `X_center_mem_cornerDisc`, `X_junction_junction`,
`X_curveMap_straight_eq_edgePoint`, `X_straight_same_edge`, `X_straight_straight`.
Before `order_τ`: `X_τ_lt_iff`.
Before `iteratedDeriv_curveMap_a`: `X_iteratedDeriv_eq_zero_of_eqOn_open` (general: `f : ℝ → Plane` `C^∞`, constant
on an open set, ⇒ `iteratedDeriv m f = 0` on its closure for `m ≥ 1`), `X_contDiff_deriv_curveMap`,
`X_deriv_curveMap_straight`, `X_iteratedDeriv_curveMap_b` (the `_b` leaf is `exact` of it, since `_a` comes first in the file and I wanted one shared proof pattern).

The helpers are not `private` (as in U_G1); the assembler may add `private` if wanted — nothing outside `section doubles`
uses them. `X_iteratedDeriv_eq_zero_of_eqOn_open` is the `Plane`-valued analogue of U_P's private
`P_iteratedDeriv_eq_zero_of_eqOn_open`; the two could be merged into one lemma over a normed space.

## Library / Mathlib notes (pin, grep-verified)

- **`regular_adjacent_meet` (SM/CS3.lean:84) is NOT in the import closure of the file** (`SM.CS3` is not reachable from
  `SM.FrontSmooth`, `SM.TurnLift`, `SM.LinkDiagramRecord`; checked by a transitive-import script). Its statement is
  exactly what `doubles_curveMap` needs and it is correct; I re-proved it verbatim as `X_regular_adjacent_meet`
  (`hQ : Regular Q`, `i`, `x ∈ edgeSegment Q i`, `x ∈ edgeSegment Q (i+1)` ⇒ `x = Q (i+1)`) from
  `principalAngle_eq_zero_iff`, `principalAngle_zero_iff_det_zero` (SM/RegularPairs.lean:70/85),
  `intersection_parameters_unique` (SM/Segment.lean:55), `edgePoint_injective`, `edgePoint_zero/one`
  (SM/G1Consequences.lean:13/16), all imported. Do not add `import SM.CS3` (it pulls in the CS lane).
- `edgePoint_injective` (SM/Crossings.lean:88): `{P} {i} (h : edge P i ≠ 0) : Function.Injective (edgePoint P i)` —
  verified, used as stated.
- Accepted declarations used exactly as in PLAN §5: `Shadow.isCrossing_pair`, `Shadow.eq_other_of_mem_of_ne`,
  `Shadow.not_adjacent_other`, `Shadow.seg_inter_other_nonempty`, `Shadow.single_adjacent_iff`,
  `Shadow.single_strand_eta`, `Shadow.singleStrandEquiv`, `Generic.common_point_unique`,
  `Generic.crossingPoint_injective`, `Diagram.crossingParam_spec/_lt_one`, `Diagram.twin`, `cycBetween`, `visitCoord`
  (`= traversalKey (visitPt v).2`, definitionally `label.val + crossingParam`), `incident`, `adjacent`.
- Mathlib names that worked (some differ from older spellings): `mul_div_cancel₀ : b * (a / b) = a`,
  `mul_div_cancel_left₀ : a * b / a = b`, `div_mul_cancel₀`, `add_sub_cancel : a + (b − a) = b`, `add_sub_cancel_left`,
  `add_sub_add_left_eq_sub`, `div_lt_div_iff_of_pos_right`, `div_lt_div_of_pos_right`, `mul_lt_mul_iff_of_pos_right`,
  `div_left_inj'`, `mul_left_inj'`, `sub_left_inj`, `Finset.sum_le_sum_of_subset_of_nonneg` + `Finset.range_mono`,
  `ZMod.val_natCast_of_lt`, `ZMod.natCast_zmod_val`, `ZMod.val_injective`, `ZMod.val_lt`, `Nat.find_spec/find_min/find_min'`,
  `Nat.exists_eq_succ_of_ne_zero`, `Function.Periodic.sub_int_mul_eq`, `Int.self_sub_floor`, `Int.fract_nonneg/lt_one`,
  `sign_mul`, `sign_pos` (SignType), `Set.EqOn.iteratedDeriv_of_isOpen` (IteratedDeriv/Lemmas.lean:441),
  `Set.EqOn.closure`, `ContDiff.continuous_iteratedDeriv m h (by exact_mod_cast le_top)`, `iteratedDeriv_const`,
  `iteratedDeriv_succ'`, `closure_Ioo (hab : a ≠ b)`, `contDiff_infty_iff_deriv`, `linear_combination` over `ZMod C.k`.
- Pitfalls: a docstring must follow `omit h in` (not precede it); `rw [← X_smul_normalize hv]` rewrites *every*
  `edge C.P j` including the one inside `normalize` — state the needed vector identity as a `have` first;
  `incident i j` is `j = i − 1 ∨ j = i` (rewrite with `← hji` in the second case).

## Notes for the assembler / executor

- All 15 statements are true exactly as stated; no hypothesis is missing. The margins are generous: the construction
  only needs `ε < |δ_j|/2` for the straight parts and `ε < dist(crossing, corner)` for `τ_mem_straight`, while the
  clearance gives `3ε`.
- `cover` appears in the file after `range_curveMap_outside` and `doubles_curveMap`, which need it; hence the
  duplicate `X_cover` (the leaf is a one-line `exact`). If the assembler reorders the chain, `cover` can move up and
  `X_cover` be dropped.
- `str_pos h (_hj : j < C.k)` (Unit G, proved in the skeleton) does not need its `j < C.k` hypothesis: `str C ε j`
  is positive for every `j : ℕ` because the cast `(j : ZMod C.k)` is periodic (`X_str_pos`). Consequently `a` is
  monotone on all of `ℕ` (`X_a_mono`), not only on `0..k`.
- `doubles_curveMap` uses only the closed-disc lemma `juncArc_mem_disc` plus `cornerDisc_disjoint`; the open-disc
  lemma `juncArc_mem_open_disc` (A) is not needed for the junction–straight case, because the open straight parts
  avoid the closed discs (`curveMap_straight_notMem_discs`). `juncArc_mem_open_disc` is therefore unused by Unit X
  (it remains referenced nowhere in the chain as far as I can see; the assembler may keep it as an export or drop it).
- Black boxes relied on, by unit: A `juncArc_mem_disc`, `juncArc_injOn`, `juncLen_pos`; G1 `dirOf_θu`,
  `three_mul_lt_edgeLength`; G2 `Θ_smooth`, `Θ_on_straight`, `curveMap_on_junction`, `curveMap_on_straight`,
  `integral_tangentField_period` (through `curveMap_periodic`); E `cornerDisc_disjoint`, `cornerDisc_disjoint_edge`,
  `three_mul_lt_dist_crossing`. Not used: `juncArc_mem_open_disc`, `cornerDisc_inter_edge_out/in`,
  `crossingPoint_notMem_cornerDisc`, `dirOf_θu_add_turn`, `curveMap_a/b`, the lift leaves (G3).
- Compile time of the whole file ≈ 7 s on this pod.
