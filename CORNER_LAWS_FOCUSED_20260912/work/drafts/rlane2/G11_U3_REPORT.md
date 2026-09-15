# G11_U3_REPORT — unit U3 (B subdivision + P parameters + disc D1–D2)

Written 2026-09-14 by the U3 prover on Mark's RunPod home pod. File: `work/drafts/rlane2/G11_U3.lean`
(2573 lines; the skeleton had 1086). Compile: `cd work/lean && lake env lean ../drafts/rlane2/G11_U3.lean`
→ exit 0, **0 errors, 0 warnings other than the 40 `declaration uses sorry` of the other units' leaves**
(~15 s). `grep -c sorry`: 50 → 41 (the 9 leaves of U3 closed; the remaining 41 = 40 leaf sorries of
units U1, U2, U4, U5, U6 and X2 + the word `sorry` in the header docstring). `diff` against
`G11_Skeleton.lean`: the ONLY removed lines are the nine `  sorry` bodies; every definition, statement,
name and docstring is byte-identical (the leaf header lines `theorem … := by` are kept and the proofs
start with `exact` where they are terms).

`#print axioms` of the nine leaves: `[propext, Classical.choice, Quot.sound]`, plus `SM.lit_homfly` for
`homfly_M₀` (through the accepted `homfly_planar`), i.e. no `sorryAx` — the U3 leaves do not depend on
any other unit's leaf.

## Leaves proved (9/9)

| leaf | line (U3 file) | how |
|---|---|---|
| `X₀_generic` (B1) | `single_generic_of_reindexed` from `gu3_reindexed_Y₃_X₀ : Reindexed Y₃ X₀` and `gu3_Y₃_generic`, the chain `X ≅ shift (m+1) X →(+p_in) Y₁ →(+m₀) Y₂ →(+p_out) Y₃ ≅ X₀` with the accepted `single_generic_shift` and `single_generic_appendVertex` ×3 | 
| `homfly_M₀` (B2) | five `Reparam`s `gu3_reparam₁ … gu3_reparam₅` (`reparam_positiveDiagram_single_shift`, `reparam_positiveDiagram_single_appendVertex` ×3, and the final re-indexing shift), each turned into `homfly D = homfly D'` by `homfly_planar ∘ PlanarIsotopic.of_reparam` |
| `X₀_cross_mp`, `X₀_cross_mq`, `X₀_cross_pq` (B3) | remoteness of the new labels from `gu3_remote_natCast_iff` (adjacency in `ZMod N` as a statement on naturals, closed by `omega`), the double point on the piece by `gu3_mem_edgeSegment_mB/mC` and on `p', q'` by `gu3_edgeSegment_lab` |
| `exists_Ψ₀` (B4) | the general lemma `gu3_visitIso_of_reparam`: every `ReparamData` between one-component positive diagrams induces an occurrence bijection with `visitPt (Ψ v) = mapPt (visitPt v)` (`gu3_exists_visitEquiv`), carrying twins, over bits, the cyclic order and the double points (`gu3_IsVisitIso`); composed along the five reparametrizations; the six named images by `gu3_image_eq` (same double point ⇒ same crossing by `Generic.crossingPoint_injective`; same over bit ⇒ same occurrence), the over bits computed by `gu3_overBit_pair` (positive diagram: over iff `0 < det`) and `edge X₀ mB = (t₂ − t₁) • edge X m`, `edge X₀ p' = edge X p` |
| `disc_isDisc` (D1) | `gu3_disc_convex` (direct from the definition, `module`), `gu3_disc_compact` (image of `Set.Finite.isCompact_convexHull`), nonempty interior from D2 |
| `triangle_sub_interior` (D2) | `gu3_triangle_sub_interior_disc` for every `r > 0`: the centroid is interior (`gu3_centroid_ball_subset`: an explicit ball via Cramer barycentric coordinates, `gu3_cramer`), `Convex.combo_interior_self_mem_interior` puts the homothetic pre-image `c + (y − c)/(1+r)` in `interior Δ`, and continuity of that pre-image map gives `U ∈ 𝓝 y` |
| `G11_exists_params` (P) | `K` = union of the foreign closed edges and the vertices (closed), `Δ ⊆ Kᶜ` from `clear_edge`/`clear_vertex`, `IsCompact.exists_thickening_subset_open` gives `δ`; `r := δ/(2M)` with `M` a radius bound of `Δ` about the centroid (`convexHull_min` into a closed ball) so that `U ⊆ thickening δ Δ ⊆ Kᶜ`; a second thickening `η` of `Δ` inside `interior U`; `gu3_exists_small` chooses `t₁ = t(x_mp) − δ'`, `t₂` the midpoint, `t₃ = t(x_mq) + δ'`, `λ = 1 + η/(2(‖x_pq − m₀‖+1))` with the three points `η`-close to the three double points; `theta_sub` by `convexHull_min` into the convex `interior U` |

## Helpers added (151, all `gu3_`-prefixed, each placed before the first leaf that uses it)

`gu3_adjacent_natCast_iff`, `gu3_remote_natCast_iff`, `gu3_lab_val`, `gu3_remote_lab`, `gu3_subdiv_natCast`, `gu3_subdiv_lab`, `gu3_subdiv_lab_succ`, `gu3_subdiv_mA`, `gu3_subdiv_mB`, `gu3_subdiv_mC`, `gu3_subdiv_mD`, `gu3_subdiv_mD_succ`, `gu3_X₀_mA`, `gu3_X₀_mB`, `gu3_X₀_mC`, `gu3_X₀_mD`, `gu3_X₀_mD_succ`, `gu3_mA_add_one`, `gu3_mB_add_one`, `gu3_mC_add_one`, `gu3_edge_mA`, `gu3_edge_mB`, `gu3_edge_mC`, `gu3_edge_mD`, `gu3_edgePoint_mB`, `gu3_edgePoint_mC`, `gu3_t₁_lt_t₂`, `gu3_t₂_lt_t₃`, `gu3_t₁_lt_one`, `gu3_t₂_lt_one`, `gu3_mem_edgeSegment_mB`, `gu3_mem_edgeSegment_mC`, `gu3_edgeSegment_mB_subset`, `gu3_edgeSegment_mC_subset`, `gu3_X₀_lab`, `gu3_X₀_lab_succ`, `gu3_edge_lab`, `gu3_edgeSegment_lab`, `gu3_edge_ne_zero`, `gu3_geometry`, `gu3_common_eq`, `gu3_param_interior`, `gu3_remote_of_isCrossing`, `gu3_p_ne_m`, `gu3_q_ne_m`, `gu3_mem_theta`, `gu3_mem_U`, `gu3_pt_off`, `gu3_Y`, `gu3_Y_generic`, `gu3_Y_neg_one`, `gu3_edge_Y`, `gu3_edgePoint_Y`, `gu3_edgeSegment_Y`, `gu3_u₂`, `gu3_u₃`, `gu3_u₂_pos`, `gu3_u₂_lt_one`, `gu3_u₃_pos`, `gu3_u₃_lt_one`, `gu3_u₂_mul`, `gu3_u₃_mul`, `gu3_Y₁`, `gu3_Y₂`, `gu3_Y₃`, `gu3_Y₁_neg_one`, `gu3_edge_Y₁`, `gu3_edgePoint_Y₁`, `gu3_Y₂_neg_one`, `gu3_edge_Y₂`, `gu3_edgePoint_Y₂`, `gu3_Y₂_apex`, `gu3_edgePoint_half₁`, `gu3_not_mem_half₁`, `gu3_edgeSegment_Y₁_old`, `gu3_edgePoint_half₂`, `gu3_not_mem_half₂`, `gu3_edgeSegment_Y₂_old`, `gu3_hoff₁`, `gu3_Y₁_generic`, `gu3_hoff₂`, `gu3_Y₂_generic`, `gu3_hoff₃`, `gu3_Y₃_generic`, `gu3_Y₃_natCast`, `gu3_cast_add_m`, `gu3_reindexed_Y₃_X₀`, `gu3_reparam₁`, `gu3_reparam₂`, `gu3_reparam₃`, `gu3_reparam₄`, `gu3_reparam₅`, `gu3_homfly_of_reparam`, `gu3_edgeSegment_p'`, `gu3_edgeSegment_q'`, `gu3_edge_p'`, `gu3_edge_q'`, `gu3_remote_mB_p'`, `gu3_remote_mC_q'`, `gu3_remote_p'_q'`, `gu3_pt_ext`, `gu3_pt_of_eval_eq_crossingPoint`, `gu3_mapPt_injective`, `gu3_mapPt_under`, `gu3_exists_visitEquiv`, `gu3_IsVisitIso`, `gu3_IsVisitIso_trans`, `gu3_crossingPoint_of_visitPt`, `gu3_eq_twin_of_ne`, `gu3_twin_of_visitPt`, `gu3_overBit_of_visitPt`, `gu3_cyc_of_not`, `gu3_traversalBetween_iff`, `gu3_visitBetween_of_visitPt`, `gu3_visitIso_of_reparam`, `gu3_other_congr`, `gu3_isOver_iff_det_pos`, `gu3_overBit_pair`, `gu3_bool_eq_of_iff`, `gu3_visit_ext`, `gu3_crossingPoint_symm`, `gu3_cp_mp`, `gu3_cp_mq`, `gu3_cp_pq`, `gu3_cp_v_mp`, `gu3_cp_v_pm`, `gu3_cp_v_mq`, `gu3_cp_v_qm`, `gu3_cp_v_pq`, `gu3_cp_v_qp`, `gu3_cp_w_mp`, `gu3_cp_w_pm`, `gu3_cp_w_mq`, `gu3_cp_w_qm`, `gu3_cp_w_pq`, `gu3_cp_w_qp`, `gu3_image_eq`, `gu3_a_ne_d`, `gu3_edgePoint_sub`, `gu3_det_triangle`, `gu3_mem_convexHull_three`, `gu3_cramer_core`, `gu3_cramer`, `gu3_centroid_ball_subset`, `gu3_centroid_mem_interior`, `gu3_triangle_compact`, `gu3_disc_convex`, `gu3_disc_compact`, `gu3_triangle_sub_interior_disc`, `gu3_edgeSegment_isClosed`, `gu3_exists_small`

Of these, 7 are `def`s (the rest are theorems): `gu3_Y`, `gu3_u₂`, `gu3_u₃`, `gu3_Y₁`, `gu3_Y₂`, `gu3_Y₃`, `gu3_IsVisitIso` — `gu3_Y`, `gu3_Y₁`,
`gu3_Y₂`, `gu3_Y₃`, `gu3_u₂`, `gu3_u₃` are the polygons and rescaled parameters of the subdivision chain, and
`gu3_IsVisitIso Ψ` is the Prop bundle (twins ∧ over bits ∧ `VisitBetween` ↔ ∧ same double points) that
makes the five-fold composition a one-liner (`gu3_IsVisitIso_trans`). A few helpers that do not use
`[NeZero k]` carry `omit [NeZero k] in` to silence the unused-section-variable linter.

Block layout: Block A (label arithmetic, `G11_subdiv` evaluation, off-edge fact `gu3_pt_off`, the
`appendVertex` chain, `Reindexed Y₃ X₀`) before B1; Block B (the five `Reparam`s) before B2; Block C
(`p'`, `q'` segments/edges and the three remoteness facts) before B3; Block D (reparametrization →
occurrence bijection, over bits of positive diagrams, the six double points) before B4; Block E (triangle
geometry, centroid, disc) before D1; Block F (`gu3_edgeSegment_isClosed`, `gu3_exists_small`) before the
parameter leaf. Block E/F helpers live in `namespace G11_Params` (they mention only `C`), so the
parameter leaf (outside the namespace) calls them as `G11_Params.gu3_…`.

## What the assembler / executor must know

1. **`import SM.CS3` was added** (second line of the file). `SM.CS3` (and `SM.CChamber`, which it imports)
   are built in `work/lean/.lake` but are NOT in the import closure of `RProof.X1Rows3`; the plan's route
   (the accepted `appendVertex` toolkit `single_generic_appendVertex`, `reparam_positiveDiagram_single_appendVertex`,
   `remote_insertIndex_of_remote`, …, and `reparam_positiveDiagram_single_shift`, `crossingGeometry_of_single_generic`
   from CChamber) needs it. Nothing else in the skeleton changed its elaboration under the extra import
   (0 errors, 0 new warnings). The merged file must keep this import (or the port must import `SM.CS3`).
2. **Correction to the plan's B1 note.** The `hoff` hypothesis of `single_generic_appendVertex` ("the new
   vertex lies on no other closed edge") does NOT follow from genericity alone: a point of the open edge
   `m` may be a double point of `X`. It is proved from the parameters (`gu3_pt_off`): a point of the base
   `[p_in, p_out] ⊆ Θ ⊆ interior U` is off every edge `h ∉ {m,p,q}` by `disc_clear_edge`, and off `p`, `q`
   because it would be the double point `x_mp` / `x_mq` (`crossingPoint_unique_of_geometry`) at a parameter
   `≠ t₁, t₂, t₃`. So `X₀_generic` genuinely uses `theta_sub` and `disc_clear_edge` of `G11_Params`.
3. **The re-indexing is `X₀ j = Y₃ (j + (k − 1 − m.val))`** (`gu3_reindexed_Y₃_X₀`), with the three new
   vertices of `Y₃` at the labels `k, k+1, k+2` (`gu3_Y₃_natCast`) and `Y = shift (m+1) X` so that `m` is the
   closing edge `-1`. The rescaled parameters are `u₂ = (t₂ − t₁)/(1 − t₁)`, `u₃ = (t₃ − t₂)/(1 − t₂)`.
4. Facts other units will want (all proved here, statements in the file):
   `gu3_edge_mA/mB/mC/mD` (`edge X₀ mB = (t₂ − t₁) • edge X m`, …), `gu3_edgePoint_mB/mC`,
   `gu3_mem_edgeSegment_mB/mC`, `gu3_edgeSegment_mB_subset/mC_subset` (pieces ⊆ `edgeSegment X m`),
   `gu3_X₀_lab`, `gu3_X₀_lab_succ`, `gu3_edge_lab`, `gu3_edgeSegment_lab` (old edges unchanged),
   `gu3_edge_p'/q'`, `gu3_edgeSegment_p'/q'`, `gu3_remote_lab`, `gu3_remote_mB_p'`, `gu3_remote_mC_q'`,
   `gu3_remote_p'_q'`, `gu3_remote_of_isCrossing`, `gu3_common_eq` (a common point of two crossing edges
   is the double point), `gu3_param_interior`, `gu3_pt_off`, `gu3_mem_theta`, `gu3_mem_U`,
   `gu3_cp_mp/mq/pq` (the double points of `X₀`'s three local crossings are those of `X`),
   `gu3_cp_v_*`, `gu3_cp_w_*` (the double points of the twelve named occurrences),
   `gu3_isOver_iff_det_pos` / `gu3_overBit_pair` (over bit of a one-component positive diagram = sign of
   `det`), `gu3_visit_ext` (same crossing + same over bit ⇒ same occurrence),
   `gu3_pt_of_eval_eq_crossingPoint` (a traversal point tracing a double point is one of its two
   occurrences — useful for U5's `Clean`/arcs and U6's gap argument), `gu3_visitIso_of_reparam`
   (general: `Reparam` of one-component positive diagrams ⇒ occurrence bijection with `gu3_IsVisitIso`),
   `gu3_traversalBetween_iff` (a cyclic-order-preserving bijection of parameter circles preserves it both
   ways), `gu3_det_triangle` (the three double points are not collinear), `gu3_centroid_mem_interior`,
   `gu3_triangle_compact`, `gu3_disc_convex`, `gu3_disc_compact`, `gu3_triangle_sub_interior_disc` (for
   every `r > 0`), `gu3_mem_convexHull_three` (barycentric membership), `gu3_edgeSegment_isClosed`.
5. The `gu3_IsVisitIso` bundle is a `def` (Prop). If the assembler prefers no new `def`s, inline its four
   conjuncts; nothing else depends on it being a constant.

## Mathlib / library pitfalls met

* `if_pos` / `if_neg` are deprecated in this Mathlib: use `ite_eq_left h` / `ite_eq_right h` (as CS3.lean does).
* After `split_ifs`, hypotheses like `i.val + 3 = 0` are simplified to `False` inside `∧`, and `omega` then
  fails on the goal; `simp only [and_false, or_false]` first (see `gu3_remote_lab`).
* `omega` does not see `k + 3`-modular arithmetic, so adjacency in `ZMod N` is first converted to a statement
  on naturals (`gu3_adjacent_natCast_iff`, via `ZMod.natCast_eq_natCast_iff'` and `Nat.mod_eq_of_lt`).
* `rw` fails "under implicit transparency" on terms whose type only becomes right after unfolding
  `positiveDiagram`/`comp`/a `set` variable (e.g. `overBit v` with `v : (single A).Visit`): use `show`,
  `Iff.trans`, `exact` or explicit `have … : … := rfl` bridges instead (`gu3_overBit_pair`,
  `gu3_visitBetween_of_visitPt`, `gu3_crossingPoint_symm` uses `simp only [Shadow.positiveDiagram_Γ]` first).
* Dependent rewriting of `overStrand x` inside `other x (over_mem x)` is impossible; use
  `gu3_other_congr` (proof-irrelevant congruence of `other`).
* `field_simp` cannot clear a denominator that has been expanded into coordinates (`u1*v2 - u2*v1` vs
  the hypothesis `u1*v2 - v1*u2`); keep `det u v` atomic and cancel with `smul_right_injective` instead
  (`gu3_cramer`).
* Non-existent names in this Mathlib: `mul_neg_iff_of_pos_left`, `div_lt_div_iff_of_pos`, `Bool.true_ne_false`,
  `Bool.eq_iff_iff` (not found by grep); used `mul_pos_iff_of_pos_left` with `← mul_neg`, `div_lt_iff₀`,
  `Bool.noConfusion`, and a two-line `gu3_bool_eq_of_iff`. `Set.Finite.isCompact_convexHull` takes the field
  `ℝ` explicitly. `add_sub_cancel : a + (b − a) = b`, `add_sub_cancel_left : a + b − a = b`.
* `push_neg` is deprecated (warning) — `rw [not_or]` used instead.
* `module` (Mathlib.Tactic.Module) is available and closes all the vector identities here.
* Deprecated-lemma and unused-variable warnings were all removed; the final log contains only the 40
  `declaration uses sorry` lines of the other units.
