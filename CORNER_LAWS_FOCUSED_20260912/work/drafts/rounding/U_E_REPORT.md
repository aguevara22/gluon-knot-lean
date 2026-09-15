# U_E report — Unit E: the clearance and the disc package (cf:lem-rounding)

File: `work/drafts/rounding/U_E.lean` (copy of `Skeleton_FINAL.lean`; only the section `discs`, lines 942-1305,
was touched). Prover: Claude (Fable 5.1), 2026-09-14.

Check: `cd work/lean && lake env lean ../drafts/rounding/U_E.lean` — exit 0, **0 errors**, 43 warnings, all of them
`declaration uses sorry` from the other units (none inside lines 942-1305; 0 deprecation or other warnings).
`grep -c sorry`: **54 before → 45 after** (the 9 leaves of Unit E). `#print axioms` on each of the nine leaves
(checked on a scratch copy of the same section): `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
Every original statement line of the section is present byte-for-byte (script-checked); everything outside the
section is unchanged (script-checked).

## Leaves proved (9 / 9)

| leaf | proof idea |
|---|---|
| `clearance_pos` | `mul_pos` + `lt_min` on the four η's; each via `Finset.lt_inf'_iff`. `η_v`: `far` positive on the finite set `otherCorners` (corners distinct, `E_corner_injective`); `η_e`: `nonIncidentEdges` is a finite union of compact segments (`Set.Finite.isCompact_biUnion`), nonempty via the edge `i+1` (`E_not_incident_succ`, needs `2 ≠ 0` in `ZMod k`, `k ≥ 3`), corner off it by `tail_off`; `η_ℓ`: `euclideanLength_pos` from `Regular`; `η_X`: case split on `Nonempty Crossing` (`ite_eq_left/right`), the crossing point is not a corner (`E_crossingPoint_ne_corner`) |
| `cornerDisc_isDisc` | convex: disc = `planeComplex ⁻¹' closedBall` and `Convex.is_linear_preimage` (`IsLinearMap ℝ planeComplex`); compact: closed (`isClosed_le`) and contained in the sup-metric `closedBall (C.P i) ε` (`E_dist_le_eucDist`), `Metric.isCompact_of_isClosed_isBounded`; interior nonempty from the next leaf |
| `mem_interior_cornerDisc` | the sup-ball of radius `ε/2` lies in the disc: `‖z‖ ≤ |re z| + |im z|` (`Complex.norm_le_abs_re_add_abs_im`) |
| `cornerDisc_disjoint` | `η_v ≤ far(q_i, otherCorners) ≤ |q_i − q_j| ≤ |p − q_i| + |p − q_j| ≤ 2ε`, against `3ε < 3·clearance ≤ η_v`; `linarith` |
| `cornerDisc_disjoint_edge` | `η_e ≤ far(q_i, nonIncidentEdges) ≤ |q_i − p| ≤ ε`, against `3ε < η_e` |
| `crossingPoint_notMem_cornerDisc` | from `E_three_mul_lt_dist_crossing` (`3ε < |x − q_i|`) and `ε > 0` |
| `cornerDisc_inter_edge_out` | `ext`; `p = q_i + t δ_i` has `eucDist = t|δ_i|` (`euclideanLength_smul`); `r := t|δ_i|`, conversely `t := r/|δ_i| ≤ 1` because `ε ≤ |δ_i|` (`E_ε_le_edgeLength`) |
| `cornerDisc_inter_edge_in` | same, after rewriting `edgePoint C.P (i−1) t = q_i − (1 − t) δ_{i−1}` (`sub_add_cancel` on `i − 1 + 1`, `module`) |
| `three_mul_lt_dist_crossing` | `η_X ≤ far(q_i, crossingPts) ≤ |x − q_i|` (`ηX` unfolds with `ite_eq_left ⟨x⟩`), `3ε < 3·clearance ≤ η_X` |

## Leaves left

None.

## Helpers added (33, all `theorem`, prefix `E_`, inside `section discs` before the leaves that use them)

`E_planeComplex_add`, `E_planeComplex_sub` (both `rfl`; `SM.planeComplex_sub` lives in `SM/CyclicComplexSeed.lean`,
which this file does not import), `E_eucDist_eq` (`eucDist p q = dist (planeComplex p) (planeComplex q)`),
`E_eucDist_comm`, `E_eucDist_triangle`, `E_eucDist_add_left` (`eucDist (p + v) p = euclideanLength v`),
`E_eucDist_sub_left`, `E_dist_le_eucDist` (sup distance ≤ Euclidean), `E_eucDist_le_add` (Euclidean ≤ sum of
coordinate distances), `E_continuous_eucDist`, `E_far_le` (`far p S ≤ eucDist p q` for `q ∈ S`), `E_far_pos`
(`far` positive on a nonempty compact set missing `p`), `E_edge_ne_zero` (from `gen.regular 0`), `E_two_ne_zero`
(`(2 : ZMod C.k) ≠ 0`), `E_not_incident_succ` (`¬ incident i (i+1)`), `E_corner_notMem_edge` (`tail_off` in the
`incident` vocabulary), `E_corner_injective` (corners of a generic polygon are distinct), `E_crossingPoint_ne_corner`,
`E_edgeSegment_isCompact`, `E_ηv_pos`, `E_ηe_pos`, `E_ηℓ_pos`, `E_crossingPts_isCompact`, `E_ηX_pos`,
`E_three_mul_clearance_le` (`3·clearance ≤ η_v ∧ … ≤ η_e ∧ … ≤ η_ℓ ∧ … ≤ η_X`), `E_cornerDisc_eq_preimage`,
`E_cornerDisc_convex`, `E_cornerDisc_isClosed`, `E_cornerDisc_subset_closedBall`, `E_mem_interior_cornerDisc`,
`E_ηX_le` (`η_X ≤ eucDist (crossingPoint x) (C.P i)`), `E_three_mul_lt_dist_crossing` (the leaf, stated on
`(Shadow.single C).Crossing`), `E_ε_le_edgeLength` (`ε ≤ |δ_i|` at an admissible `ε`).

Possibly useful to Unit X / the assembler (all polygon-only, no `sorry` behind them): `E_eucDist_eq`,
`E_eucDist_triangle`, `E_dist_le_eucDist`, `E_edge_ne_zero`, `E_corner_injective`, `E_crossingPoint_ne_corner`,
`E_three_mul_clearance_le`, `E_ε_le_edgeLength`, `E_eucDist_add_left/sub_left`.

## Mathlib names in this pin (v4.34.0-rc2 pin) — what was checked or was missing/misspelled

- `IsClosed.notMem_iff_infDist_pos` is the spelling (HausdorffDistance.lean:583): `IsClosed s → s.Nonempty →
  (x ∉ s ↔ 0 < infDist x s)`. `IsClosed.not_mem_iff_infDist_pos` does not exist.
- `if_pos` / `if_neg` are **deprecated** here (warnings): use `ite_eq_left (hc : c) : (if c then t else e) = t` and
  `ite_eq_right (hc : ¬c)`. `ite_cond_eq_true` is deprecated too (→ `ite_eq_left_of_eq_true`).
- `Set.mem_setOf_eq` is deprecated → `Set.mem_ofPred_eq`.
- `ZMod.natCast_zmod_eq_zero_iff_dvd` / `ZMod.natCast_self_eq_zero` do not exist; use
  `CharP.cast_eq_zero_iff (ZMod C.k) C.k : ((n : ℕ) : ZMod C.k) = 0 ↔ C.k ∣ n` (then `Nat.le_of_dvd` + `omega`
  against `C.hk`).
- Available as expected: `Finset.lt_inf'_iff`, `Finset.inf'_le`, `Metric.infDist_le_dist_of_mem`,
  `Set.Finite.isCompact_biUnion`, `Set.Finite.isCompact`, `Metric.isCompact_of_isClosed_isBounded`,
  `Convex.is_linear_preimage`, `Complex.abs_re_le_norm`, `Complex.abs_im_le_norm`,
  `Complex.norm_le_abs_re_add_abs_im`, `Prod.dist_eq`, `Real.dist_eq`, `Complex.dist_eq`, `add_sub_cancel_left`
  (`a + b - a = b`), `sub_sub_cancel_left` (`a - b - a = -b`), `sub_sub_cancel`, `add_eq_left`, `exists_ne`,
  `Set.mem_biUnion`, `Set.mem_iUnion₂`, the `module` tactic.
- Library: `SM.euclideanLength_smul` (TurnLift.lean:380), `SM.euclideanLength_normalize`, `SM.edgePoint_injective`
  (Crossings.lean:88), `SM.edgePoint_zero/one` (G1Consequences.lean:13/16), `SM.Link.Shadow.incidentTail_mk_iff`,
  `Shadow.Generic.crossingPoint_mem_interior` all exist with the expected statements. `SM.continuous_planeComplex`
  (RotationContinuity.lean) is imported transitively through `SM.TurningNumber`. Note that `Shadow`, `PolyComp`,
  `Generic` etc. live in the namespace `SM.Link` (the file has `open Link`).
- Anonymous-constructor patterns `fun p ⟨j, _, hp⟩ => …` fail on `Set.Subset` binders ("expected type could not
  be determined"); use `fun p hp => by obtain … := hp; …`.

## Notes for the assembler / executor

- All nine statements were provable **as stated**; no counterexample, no missing hypothesis. In particular the
  nonemptiness of `nonIncidentEdges C i` and of `otherCorners C i` (needed because `far` is `0` on the empty set)
  holds thanks to `k ≥ 3`; the definition `ηX = ηℓ` when there is no crossing is what makes `E_ηX_pos` go through.
- `D.toDiagram.Γ.Crossing` / `D.toDiagram.Γ.crossingPoint x` reduce definitionally to `(Shadow.single C).Crossing` /
  `(Shadow.single C).crossingPoint x`; the leaves on `D` are closed by `exact` from the `Shadow.single C` versions
  (`E_three_mul_lt_dist_crossing`, `E_ηX_le`) with no transport.
- The two disc/edge intersection leaves use the hypothesis `ε ≤ |δ_i|` (from `ε < clearance ≤ η_ℓ/3`); the `i − 1`
  leaf is stated with `ZMod` subtraction on the label and needs `sub_add_cancel : i − 1 + 1 = i` only.
- The three leaves `cornerDisc_isDisc`, `mem_interior_cornerDisc`, `three_mul_lt_dist_crossing` keep their
  original `:= by` header and are closed by `exact <helper>`.
- No file under `work/lean` was written; no `lake build` was run. Scratch files are in `/tmp/ue/`.
