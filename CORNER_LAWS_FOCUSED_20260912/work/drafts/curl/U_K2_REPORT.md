# U_K2 report — Unit K2: the polygonal kink insertion (`exists_kinkInsertion`)

Prover unit K2 on a byte-identical copy of `Skeleton_FINAL.lean` (2026-09-14).

## Result

- **Leaf proved: `SM.Curl.exists_kinkInsertion`** (the single leaf of U6 K2), with its full 16-field
  `KinkInsertion` spec: `D'`, `U`, `ri : RIData U S.D D'` (frame, move match, the two arcs and their
  covers, same ends, `no_inner`, `kink`, `inner_iff'`), `kink_neg`, `c_eq`, `old`, `oldVisit`,
  `oldVisit_over/under/twin`, `old_point`, `old_sign`, `order_old`, `order_gap`, `order_pair`, `writhe`.
- **Leaves left in this unit: none.**
- File: `work/drafts/curl/U_K2.lean` (5149 lines; skeleton 1130 + ≈4020 lines of helpers).
- Check (official): `cd work/lean && lake env lean ../drafts/curl/U_K2.lean` → exit 0, **0 errors**,
  53 `declaration uses sorry` warnings (the other units' leaves; the skeleton had 54), the inherited
  `<;>` linter note at line 567, and two harmless deprecation warnings (`dif_pos`/`dif_neg`, lines
  ≈3430/3435, in `k2_over_kink`/`k2_orig_over`). Compile time ≈15 s with the built oleans.
- `grep -c sorry`: 56 before → 55 after (the 54 leaf sorries minus this leaf, plus the two prose
  mentions of the word in the header).
- Statements frozen: lines 1-897 and the tail after the leaf are byte-identical to `Skeleton_FINAL.lean`
  (checked with `diff`); the leaf's docstring/statement lines are unchanged; only its `sorry` body was
  replaced. All helpers are inserted immediately before the leaf's docstring, inside `namespace Curl`
  (same section as the leaf), in a `section K2 … end K2` with `variable (L : KinkLocation S)`.
- Axioms (checked on a scratch copy with `#print axioms`):
  `SM.Curl.exists_kinkInsertion` = `[propext, Classical.choice, Quot.sound]`;
  `SM.Curl.k2_ri` = the same. **No `sorryAx`**: the unit does not use any other unit's black box
  (in particular not U5's `RIData.crossingPoint_ψ / sign_ψ / writhe_eq`; `writhe` is proved directly).
  `SM.cf_lem_curl` still lists `sorryAx` because of the other units.

## The construction (what the assembler / executor must know)

**Four new vertices, not three.** The leaf's (frozen) docstring says "three new vertices"; the
construction uses **four**: `A = r₀ − ε d`, `B = r₀ + ε d + ε n`, `C = r₀ − ε d + ε n`, `Dv = r₀ + ε d`
with `d = dir s₀` the edge vector of the location's edge, `n = (d.2, −d.1)` (clockwise normal; the frame
`(d, n)` is negatively oriented, `det d n = −|d|²`). The edge `a` of `D` is replaced by the five edges
`e1 = [P a, A]`, `e2 = [A, B]`, `e3 = [B, C]`, `e4 = [C, Dv]`, `e5 = [Dv, P (a+1)]`. Reason: the accepted
`OutsideMatch.dir_pos` demands that every point strictly outside `U` keep its direction up to a
positive factor, so the entering and exiting new edges must lie on the line of `s₀`; a monogon with only
three new vertices then either has its two collinear pieces overlapping (not generic) or is a bump with
no crossing. With four vertices `e2` and `e4` cross at `K = r₀ + (ε/2) n`, both at parameter `1/2`
(`k2_crossingParam_kink_e2/e4`), the loop is clockwise (all four turns are right turns), and with the
later branch `e4` over, `det (dir e4) (dir e2) = −4 ε² |d|² < 0`, so `D'.sign kink = −1`
(`k2_kink_neg`), consistent with the plan's `order_pair`/`double_neg` convention. The statement is not
affected; only the docstring's "three" is inaccurate.

**Labels.** `D'` has one component (as `D`, via `S.one`; `k2_fin_eq : ∀ i, i = L.r.1`) with `k + 4`
vertices; label values: `n < a` old edge `n`; `a, a+1, a+2, a+3, a+4` = `e1 … e5`; `n ≥ a+5` old edge
`n − 4`. The kink crossing is `k2_kink = {e2, e4}` = `{k2_eS 1, k2_eS 3}`; the correspondence of the old
crossings is `k2_old` (lift of over/under strands: old strands are relabelled, `s₀` is sent to `e1` or
`e5` according to the crossing parameter), `oldVisit` is `k2_oldVisit`.

**The disc.** `U = Metric.closedBall r₀ ρ` (sup metric of `ℝ × ℝ`, as in Smoothing.lean), with
`ρ = k2_clear / 2` where `k2_clear = inf` over strands `e ≠ s₀` of `infDist r₀ (seg e)` (> 0 by
`L.off_edges`). `ε = min (t/2) ((1−t)/2) (ρ / (4‖d‖))`. The arc of `D` is `s₀` on `[θIn, θOut]`,
`θIn/Out = t ∓ ρ/‖d‖`; the kinked arc of `D'` runs from `θIn' = θIn/(t−ε)` on `e1` to
`θOut' = (θOut − t − ε)/(1 − t − ε)` on `e5` through `e2, e3, e4` (which lie in the open disc).

**Cyclic order.** `k2_f` is the explicit piecewise-linear strictly increasing map from the traversal
coordinate of `D` to that of `D'` (identity below `a`, `a + (c−a)/(t−ε)` on `[a, a+t)`,
`a + 4 + (c−a−t−ε)/(1−t−ε)` on `[a+t, a+1)`, `c + 4` above); `k2_visitCoord_lift_eq_f` identifies the
lifted coordinates, `k2_side` places every old occurrence on one side of the gap `(a+1, a+4)`, the kink
occurrences have coordinates `a + 1 + 1/2` (under, on `e2`) and `a + 3 + 1/2` (over, on `e4`).

**Reducibility.** `k2_comp`, `k2_shadow`, `k2_D'` are `abbrev`s (reducible); this is essential — with
plain `def`s the types `ZMod ((k2_shadow S L).comp i).k` and `(k2_D' S L).Γ.Crossing` do not unify with
`ZMod (k+4)` / `(k2_shadow S L).Crossing` at instance/`rw` transparency. Keep them `abbrev` when porting.

**One `set_option maxHeartbeats 1000000 in`** on `k2_dir_strandBefore_origPt` (the default budget
timed out in the final `exact`, apparently while unifying through `k2_origPt`/`clampIco`).

## Helpers added (all prefixed `k2_`, lowercase after the prefix; ≈470 declarations)

Groups, in file order:
- parameters: `k2_k k2_P k2_a k2_t k2_s₀ k2_d k2_r₀ k2_n k2_fin_eq k2_three_le k2_t_pos k2_t_lt_one
  k2_d_ne_zero k2_norm_d_pos k2_r₀_eq k2_r₀_eq_edgePt k2_tail_s₀ k2_d_eq k2_strand_eq k2_dot_d_n
  k2_dot_n_n k2_det_d_n k2_dd_pos k2_norm_n`; clearance and small parameters: `k2_others k2_mem_others
  k2_others_nonempty k2_clear k2_clear_pos k2_clear_le_dist k2_ρ k2_ρ_pos k2_ρ_lt_clear
  k2_clear_le_t_mul k2_clear_le_one_sub_t_mul k2_ε k2_ε_pos k2_ε_le_t k2_ε_le_one_sub_t k2_ε_le_ρ
  k2_four_ε_norm_le k2_ε_lt_t k2_ε_lt_one_sub_t k2_ε_norm_lt_ρ k2_two_ε_norm_lt_ρ k2_ρ_lt_t_mul
  k2_ρ_lt_one_sub_t_mul k2_θIn k2_θOut k2_ρ_div_pos k2_ε_lt_ρ_div k2_θIn_pos k2_θOut_lt_one
  k2_θIn_lt_θOut k2_θIn_lt k2_lt_θOut`.
- points, tuple, shadow, edges: `k2_A k2_B k2_C k2_Dv k2_K k2_av k2_av_lt k2_Q k2_tuple k2_comp
  k2_shadow k2_comp_k k2_comp_P k2_E k2_Q_of_le k2_Q_a1..a4 k2_Q_of_ge k2_E_of_lt k2_E_a k2_E_a1..a4
  k2_E_of_ge k2_A_sub_Pa k2_Pa1_sub_Dv k2_cast_k_sub_one_add_one k2_edge_eq`.
- strands and kinds: `k2_m k2_lab k2_lab_lt k2_dir' k2_tail' k2_edgePt' k2_mem_seg' k2_mem_interior'
  k2_kind_cases k2_IsOld k2_IsMid k2_orig k2_orig_fst k2_orig_val_of_le k2_orig_val_of_ge
  k2_orig_of_eq_a k2_orig_of_eq_a4 k2_orig_eq k2_tail_old k2_dir_old k2_edgePt_old k2_seg_old
  k2_interior_old k2_tail_e1..e5 k2_dir_e1..e5`.
- frame coordinates and disc: `k2_X k2_Y k2_dd k2_X_frame k2_Y_frame k2_frame_ext k2_eq_frame
  k2_A_frame … k2_edgePt_s₀_frame k2_pt_e1..e5 k2_mem_e1_iff..e5_iff k2_mem_int_e1_iff..e5_iff
  k2_dist_frame_le k2_dist_frame_zero k2_U k2_isDisc_U k2_interior_U k2_frontier_U k2_r₀_mem_ball
  k2_frame_mem_ball k2_not_mem_U_of_mem_seg k2_tail_not_mem_U k2_crossingPoint_not_mem_U
  k2_dist_edgePt_s₀ k2_edgePt_s₀_mem_U_iff k2_edgePt_s₀_mem_ball_iff k2_edgePt_s₀_mem_sphere
  k2_crossingParam_far`.
- adjacency by values: `k2_zmod_succ_val k2_zmod_eq_iff k2_zmod_adjacent_iff k2_zmod_incident_iff
  k2_adjacent_iff k2_incidentTail_iff k2_adjacent_iff_D k2_incidentTail_iff_D k2_val_lt_k k2_s₀_val
  k2_adjacent_old_iff k2_incidentTail_old_iff k2_orig_ne_s₀ k2_orig_injOn`.
- normalised coordinates: `k2_x k2_y k2_x_frame k2_y_frame k2_eq_frame' k2_frame_ext' k2_frame_eq_iff
  k2_mem_e1_iff'..e5_iff' k2_mem_int_e1_iff'..e5_iff' k2_mem_s₀_iff k2_mem_int_s₀_iff k2_xy_A..K
  k2_xy_Pa k2_xy_Pa1 k2_mid_mem_ball k2_mid_mem_U k2_old_not_mem_U k2_K_mem_e2/e4 k2_K_mem_int_e2/e4
  k2_K_mem_ball k2_eq_K_of_mem_e2_e4`.
- non-middle strands, meets: `k2_lab_inj k2_not_isMid_iff k2_isMid_cases k2_isOld_of_lt k2_isOld_of_ge
  k2_dir_eq_smul_orig k2_seg_subset_orig k2_interior_subset_orig k2_eq_of_orig_eq k2_e1_e5_disjoint
  k2_e1_e3_disjoint k2_e1_e4_disjoint k2_e2_e5_disjoint k2_e3_e5_disjoint k2_old_mid_disjoint
  k2_kink_int_meet k2_det_e2_e4 k2_det_e4_e2 k2_four_ε_sq_dd_pos k2_seg_pred_inter k2_seg_succ_inter
  k2_adjacent_of_lab k2_not_adjacent_lab k2_incidentTail_of_lab k2_not_incidentTail_lab
  k2_adjacent_orig_s₀_iff k2_incidentTail_orig_s₀_iff k2_incidentTail_s₀_orig_iff k2_orig_val_old
  k2_orig_val_eq k2_orig_eq_succ k2_orig_eq_pred k2_old_e1_ne_succ k2_old_e5_ne_pred
  k2_old_e1_not_adjacent k2_old_e5_not_adjacent k2_not_adjacent_orig k2_A_mem_ball..k2_Dv_mem_ball
  k2_tail_mem_U_of_not_old`.
- genericity: `k2_reg k2_reg_smul k2_zero_sub_one k2_det_e1_e2 k2_det_e2_e3 k2_det_e3_e4 k2_det_e4_e5
  k2_regular_E k2_regular k2_tail_off_old k2_tail_off_e1..e5 k2_kink_vertex_not_mem_old k2_tail_off
  k2_transverse k2_int_e1_e5_absurd k2_orig_ne_of_int k2_no_triple_mid k2_no_triple k2_generic`.
- crossings: `k2_eS k2_lab_eS k2_eq_eS k2_not_adjacent_e2_e4 k2_kink k2_kink_val k2_mem_kink_iff
  k2_crossingPoint_kink k2_meet_classify k2_eq_kink_of_mid k2_not_mid_of_ne_kink k2_isCrossing_orig
  k2_origCrossing k2_origCrossing_val k2_orig_mem_origCrossing k2_crossingPoint_orig
  k2_eq_of_orig_eq_mem k2_orig_injOn_crossing k2_origCrossing_injective k2_ν k2_liftStrand
  k2_val_ne_av_of_ne k2_lab_liftStrand_of_ne k2_liftStrand_isOld k2_liftStrand_of_s₀
  k2_liftStrand_not_mid k2_orig_liftStrand k2_crossingPoint_mem_liftStrand
  k2_adjacent_orig_s₀_of_old_e1/e5 k2_adjacent_orig_of_adjacent k2_isCrossing_lift k2_liftCrossing
  k2_liftCrossing_val k2_liftStrand_mem k2_liftCrossing_ne_kink k2_origCrossing_liftCrossing
  k2_liftStrand_orig k2_liftCrossing_origCrossing k2_old k2_old_apply`.
- the diagram, signs, occurrences: `k2_over k2_over_mem k2_over_kink k2_orig_over k2_D' k2_D'_Γ
  k2_D'_overStrand k2_D'_overStrand_kink k2_D'_underStrand_kink k2_orig_underStrand k2_kink_neg
  k2_sign_of_ne k2_old_sign k2_old_point k2_writhe k2_visit_ext k2_liftVisit k2_liftVisit_fst
  k2_liftVisit_strand k2_liftVisit_ne_kink k2_origVisit k2_oldVisit k2_oldVisit_apply
  k2_oldVisit_over k2_oldVisit_under k2_oldVisit_twin`.
- arcs, cleanness, RI site: `k2_θIn_mem k2_θOut_mem k2_arc k2_mem_arc_iff k2_inner_arc_iff
  k2_strand_eq_s₀_of_mem_U k2_eval_arc_startPt/stopPt k2_isArc_arc k2_arcCover_D k2_clean_D k2_no_inner
  k2_traversalBetween_span_four k2_θIn' k2_θOut' k2_t_sub_ε_pos k2_one_sub_t_sub_ε_pos k2_θIn'_pos
  k2_θIn'_lt_one k2_θOut'_pos k2_θOut'_lt_one k2_θIn'_mul k2_θOut'_mul k2_θIn'_mem k2_θOut'_mem k2_mA
  k2_mA_val k2_mA_add_val k2_eS_eq k2_arc' k2_inner_arc'_iff k2_plab k2_lab_pt k2_eval_pt k2_eval_e1
  k2_eval_e5 k2_eval_mem_seg k2_eval_mem_U_iff k2_eval_mem_ball_iff k2_arc'_startPt k2_arc'_stopPt
  k2_eval_arc'_startPt/stopPt k2_start_eq k2_stop_eq k2_isArc_arc' k2_pt_eq_of k2_arcCover_D' k2_clean_D'
  k2_localFrame k2_inner_iff'`.
- outside match: `k2_lp k2_lpinv k2_lp_lpinv k2_lpinv_lp k2_lp_old k2_lp_e1 k2_lp_e5 k2_lpinv_old
  k2_lpinv_e1 k2_lpinv_e5 k2_edgePt_orig k2_lp_mem k2_origPt k2_origPt_fst k2_origPt_strand
  k2_origPt_param k2_not_mid_of_not_mem_interior k2_eval_origPt k2_origPt_outside k2_liftOld
  k2_lab_liftOld k2_liftOld_isOld k2_orig_liftOld k2_liftStrand_eq_liftOld k2_exists_origPt_eq
  k2_origPt_injOn k2_origPt_bijective k2_φ k2_origPt_φ k2_φ_eval k2_φ_fst k2_φ_dir_pos k2_dir_pred
  k2_dir_strandBefore_origPt k2_φ_dir_pos_before k2_ψ k2_ψ_val k2_lp_crossingParam
  k2_crossingParam_lift k2_φ_over_eq k2_φ_under_eq k2_outsideMatch k2_moveMatch k2_ri k2_ri_kink`.
- cyclic order: `k2_e2_mem_kink k2_e4_mem_kink k2_crossingParam_kink_e2/e4 k2_visitCoord_under_kink
  k2_visitCoord_over_kink k2_visitCoord_lift k2_traversalKey_r k2_f k2_f_pos_cases k2_f_1..4
  k2_f_2_bounds k2_f_3_bounds k2_f_strictMono k2_coord_cases k2_visitCoord_lift_eq_f k2_side
  k2_cycBetween_congr k2_cycBetween_map k2_order_old k2_kink_coord_mem k2_order_gap k2_order_pair`.

Accepted library used (beyond Mathlib): `Diagram`/`Shadow` API of SM/LinkDiagram.lean, `cycBetween`,
`visitCoord`, `twin` of SM/LinkDiagramRecord.lean, `IsDisc`, `Arc`, `IsArc`, `ArcCover`, `OutsideMatch`,
`Clean`, `LocalFrame`, `MoveMatch`, `RIData` of SM/LinkMoves.lean, and the SM.Link-level helpers of
SM/Smoothing.lean (`Shadow.edgePt`, `Generic.seg_inter_succ`, `mk_sub_one_ne`, `tail_mem_seg_pred`,
`head_mem_seg_succ`, `dist_edgePt`, `isClosed_seg`, `regularPair_smul_pos`,
`regularPair_of_det_ne_zero`, `det_smul_smul`, `clampIco`, `Shadow.mk_eq_mk_iff`,
`Diagram.crossingParam_congr`, `Diagram.visitCoord_eq`) plus, from the `Smoothing` namespace, the
general lemmas `Smoothing.zval_add_one_of_lt/eq`, `zval_sub_one_of_pos/zero`, `zcast_sub_self`,
`zcast_pred`, `Strand_eq_mk_val`, `Strand_mk_eq_mk_iff`, `eval_eq_edgePt`, `eval_mem_seg`,
`Pt_eq_mk_strand`, `Pt_ext`, `arc_inner_iff_of_same_edge`, `arc_mem_iff_of_same_edge`,
`isArc_eval_mem_of_mem`. SM.Smoothing is imported transitively through `SM.PolynomialBlock`; the ported
`SM/Curl.lean` must keep that import (or import `SM.Smoothing`).

## Mathlib / Lean pitfalls met (pin 85e3a25e, Lean v4.34.0-rc2)

- `le_or_lt` is gone: use `le_or_gt`. `if_pos/if_neg` are deprecated (`ite_eq_left/ite_eq_right` work as
  drop-in `rw` lemmas); `dif_pos/dif_neg` still work with a warning. `push_neg` deprecated (`push Not`).
- `Fintype.sum_eq_add_sum_subtype_ne` must be stated with the summand over exactly the type whose
  `Fintype` instance appears in the goal (`(k2_D' S L).Γ.Crossing`, not `(k2_shadow S L).Crossing`), and
  the subtype sum then has to be reconciled by `show` before `Equiv.sum_comp` (`rw` fails at implicit
  transparency across `(k2_D' S L).Γ` vs `k2_shadow`).
- `omega` treats an `abbrev` and its unfolded form as different atoms (e.g. `k2_lab S L u` vs
  `(k2_m S L u).val`, `k2_av S L` vs `(k2_a S L).val`, the ZMod modulus `((k2_shadow S L).comp i).k` vs
  `k2_k S L + 4`): add `have : … = … := rfl` links before `omega`. Likewise `ZMod.val_lt m` must be
  taken *after* destructuring so that its modulus is the literal one.
- `rw` with a variable that other hypotheses depend on (`u` inside `other y hu`, `p` inside a proof
  `hmem`) fails with "motive is not type correct": rewrite the other term first, or `subst`.
- `field_simp` needs the nonzero-denominator facts as hypotheses in context (`k2_t S L − k2_ε S L ≠ 0`).
- `positivity` cannot see `1 − t − ε > 0`; give explicit `mul_pos`/`nlinarith`.
- Anonymous-constructor `⟨x, h₁, h₂⟩ : Set.Ico 0 1` elements are accepted as terms but make `rw`
  motives fail later; prefer a named membership proof `⟨x, hmem⟩`.
- `Real`-valued `if`s inside `clampIco`: unifying through them can blow the heartbeat budget
  (hence the one `set_option maxHeartbeats`).
