# W3_A1_BC_REPORT — unit W3-A1 first prover (Units B–C copy + 18 sub-leaves), Wave 3 row 177

Prover BC (subagent), 2026-09-15 21:21–21:40 UTC / 5:21–5:40pm ET (bounded test, audit A-177-1; hard stop
00:15 UTC not needed).  Inputs: `W3_SKELETON_REPORT.md` §1.1, §2.0–2.2, §3, §5, §6 W3-A1; `Skeleton_W3.lean`
(1231 lines, 30 sorry); `RProof/GenericTransport.lean` 235–4917 (the source of the copy), 5511–5935 (the
C-free `GU6Single` helpers), 7001–7044 (`gu6_y_*_ne_*`), 7053–7162 (`gu6_Rmp_iff`, `gu6_ov_*`), 8635–8770
(`gu3_edgeSegment_isClosed`, `gu3_exists_small`, `G11_exists_params`).  Nothing under `work/lean` written.

## 0. Result

| item | value |
|---|---|
| file | `work/drafts/moves/W3_A1_BC.lean` — **5161 lines** |
| compile `cd work/lean && lake env lean ../drafts/moves/W3_A1_BC.lean` | exit 0, **0 errors**, 44 s; warnings: 12 × `declaration uses sorry` + the skeleton's 14 cosmetic `if_pos`/`if_neg` deprecations |
| `grep -c sorry` | skeleton **30** → **12** (every remaining `sorry` is a sub-leaf body outside this unit: `w3b_reparam_switch`, `w3a_riii_param`, `w3a_exists_Ψ₁` (DE prover), `w3e_xs_point`, `w3e_liftVisit_σD_sw`, `w3e_recordIsoData_sw`, `w3g_*` ×2, `w3h_*` ×4) |
| lines copied | **3697** (the transformed text of GenericTransport 262–4917 after deleting the 66 C-free helpers; the wrapper `section W3A1Copy … end W3A1Copy` is lines 241–3951 of the file) |
| declarations in the copy | 579 declarations in the source range; 1 structure (`G11_Params`) replaced by the skeleton's `G11_ParamsSw`, 66 C-free helpers NOT copied (reused by name), the remaining 512 copied into `SM.Link.G11_ParamsSw` under `G11_Config → G11_ConfigSw`, `G11_Params → G11_ParamsSw`, `G11_discOf → G11_discOfSw`, `G11_centroid → G11_centroidSw`; every `gu*` name kept |
| **closed (18)** | `w3a_X₀_generic`, `w3a_X₁_generic`, `w3a_X₀_cross_mp/mq/pq`, `w3a_X₁_cross_pC/qB/pq`, `w3a_y_ne`, `w3a_y'_ne`, `w3a_over_mp₀/mq₀/pq₀/mp₁/mq₁/pq₁`, `w3a_exists_Ψ₀`, `w3a_exists_params` |
| open (this unit) | none |
| statement identity | `check_W3_identity.py Port_GenericTransportSw_draft.lean W3_A1_BC.lean`: the five frozen blocks IDENTICAL, imports OK, exit 0; all **42** `w3a_…w3h_` statements (`^theorem w3x_… := by`) byte-identical to `Skeleton_W3.lean`; every non-`w3` declaration NAME of the skeleton is still declared in the file |
| `#print axioms` (scratch copy) | all 18 closed leaves and the last copied theorem `G11_ParamsSw.exists_arcCovers`: `[propext, Classical.choice, Quot.sound]` — standard only, no `sorryAx`; `G11_core_sw` still carries `sorryAx` through the DE leaves, as expected |

## 1. How the copy was made (script: scratch `build_bc.py`; sed-mechanical as prescribed)

1. Declarations of GenericTransport 235–4917 were listed (579); their TYPES were obtained by one Lean run of
   `#check @RProof.G11_Params.<name>` for each, and a declaration was classified **C-free** iff its type mentions
   none of `G11_Config`, `G11_Params`, `G11_discOf`, `G11_centroid` (reliable: a `C.X`/`π.…` in the statement
   forces the binder).  66 are C-free (66 vs the report's estimate 148 for the whole 235–8630); their blocks
   (docstring / `omit … in` / attributes / indented body) were deleted and the names are made visible by ONE
   scoped `open RProof.G11_Params (…)` inside the copy's namespace, so the copied proofs use them unqualified
   exactly as the accepted proofs do.  The list: gu3_IsVisitIso gu3_adjacent_natCast_iff gu3_bool_eq_of_iff gu3_centroid_ball_subset gu3_cramer gu3_cramer_core gu3_crossingPoint_of_visitPt gu3_crossingPoint_symm gu3_cyc_of_not gu3_edgePoint_sub gu3_eq_twin_of_ne gu3_exists_visitEquiv gu3_homfly_of_reparam gu3_isOver_iff_det_pos gu3_lab_val gu3_mapPt_injective gu3_mapPt_under gu3_mem_convexHull_three gu3_other_congr gu3_overBit_of_visitPt gu3_overBit_pair gu3_pt_ext gu3_pt_of_eval_eq_crossingPoint gu3_remote_lab gu3_remote_natCast_iff gu3_remote_of_isCrossing gu3_subdiv_lab gu3_subdiv_lab_succ gu3_subdiv_mA gu3_subdiv_mB gu3_subdiv_mC gu3_subdiv_mD gu3_subdiv_mD_succ gu3_subdiv_natCast gu3_traversalBetween_iff gu3_twin_of_visitPt gu3_visitBetween_of_visitPt gu3_visit_ext gu4_cramer gu4_crossingPoint_mem_interior gu4_crossingPoint_mem_pair gu4_det_add_left gu4_det_add_right gu4_det_self gu4_det_smul_left gu4_det_smul_right gu4_det_sub_left gu4_det_sub_right gu4_eq_of_det_eq gu4_gen_regular gu4_gen_tail gu4_gen_trans gu4_gen_triple gu4_mem_edgeInterior_iff gu4_mem_edgeSegment_iff gu4_mem_edgeSegment_of_convex gu4_ne_of_remote gu4_remote_of_isCrossing gu4_sub_of_mem_edge gu5_both gu5_edgePoint_eq gu5_edgePoint_mem_segment gu5_edgeSegment_eq_segment gu5_entry gu5_exit gu5_pt_ext 
2. Substitutions on the remaining text (word-boundary regex): `G11_Config → G11_ConfigSw`, `G11_Params → G11_ParamsSw`,
   `G11_discOf → G11_discOfSw`, `G11_centroid → G11_centroidSw`.  No other edit was needed: **the copy compiled
   with 0 errors at the first attempt** (22 s for the copy alone).  All `C.*` accessors used by the range
   (`m X p q hmp hmq hpq gen hk comp D₀ v_* order`) exist on `G11_ConfigSw`.
3. Placement (small deviation from "immediately after line 207", forced by dependencies): the copy's structure
   needs `G11_discOfSw`, so the skeleton's block `/-! ### W3-(a) … -/` + `G11_centroidSw` + `G11_discOfSw` +
   `structure G11_ParamsSw` (its own text, with the `{k : ℕ} [NeZero k]` binder) was moved up to directly after
   `end G11_ConfigSw` (line 199 of the skeleton — the report's "207" was off by 8), and the copy follows it as
   `section W3A1Copy / open SM.GeoCarrier SM.Carrier / namespace G11_ParamsSw / variable … / open RProof.G11_Params (…)
   / <copy> / end G11_ParamsSw / end W3A1Copy` (the two extra `open`s mirror the accepted file's header and are
   scoped to the copy).  Then the skeleton continues unchanged (W3Switch, the `w3a_` block, D8′, E′, the leaf, W3E,
   Row177_6).
4. Skeleton declarations that DUPLICATED copied ones were removed from the skeleton part (the copy's version is
   now the definition): `hk₃ X₀ mid mA mB mC mD p' q' apex X₁ U M₀ M₁ M₀_componentCount M₁_componentCount` and
   `w_mp w_pm w_mq w_qm w_pq w_qp`.  All are definitionally the skeleton's (`M₀` uses `π.X₀_generic` instead of
   `π.w3a_X₀_generic` — proof-irrelevant; the copy's `w_*` use `⟨k + 3, π.hk₃, π.X₀⟩` where the skeleton wrote
   `π.comp₀` — `comp₀` unfolds to it).  The skeleton-only names `comp₀ comp₁ st₀ st₁ y_* y'_* w'_* *_fst x₀ x₁
   M₀sw M₁sw` and every `w3*` statement are untouched; downstream (D8′, E′, `G11_core_sw`, W3E) compiled unchanged.

## 2. The 18 sub-leaf proofs (connectors; new material is `w3bc_`-prefixed)

* `w3a_X₀_generic := π.X₀_generic`, `w3a_X₁_generic := π.X₁_generic`, the six `w3a_X*_cross_* := π.X*_cross_*`
  (`exact`; `π.comp₀` vs `⟨k + 3, π.hk₃, π.X₀⟩` is defeq).
* `w3a_y_ne` / `w3a_y'_ne`: the accepted `gu6_y_*_ne_*` :7016–7044 with the C-free
  `RProof.G11_Params.gu6_xPair_ne_of_not_mem` (qualified) and the copy's label facts `gu5_mB_ne_mC`, `gu5_p'_ne`,
  `gu5_q'_ne`, `gu5_p'_ne_q'` in place of `gu6_mB_ne_mC`/`gu6_lab_ne_mB/mC`/`gu6_p'_ne_q'` (D8-region, not copied).
* `w3a_over_*`: three C-free helpers added before them inside `namespace G11_ParamsSw`:
  `w3bc_over_under_pos/neg` (the accepted `gu6_over_under_of_pos/neg` :5879/5904 read on STRANDS via
  `congrArg (·.2.val)` and `gu6_sv_strand`) and `w3bc_det_pos_iff_of_sign_eq` (`GT_det_pos_iff_of_sign` through
  `crossingSign`).  The determinant transfer uses the copy's `gu4_edge_X₀_mB/mC/p'/q'` (+ `CV.det_smul_left'`, the
  factors `t₂ − t₁`, `t₃ − t₂` from `π.h₁…h₄`) on the `M₀` side, `X₁_sign_pC`/`X₁_sign_qB` + `det_swap` and
  `gu4_edge_X₁_eq` on the `M₁` side, and the skeleton's `C.det_mp/mq/pq_ne` for the negative cases.
* `w3a_exists_Ψ₀`: the copy's `exists_Ψ₀` (ten clauses) + the three crossing-correspondence clauses from
  `w3b_fst_eq_iff_of_twin Ψ₀ htw v C.v_*` rewritten with the images and `w_*_fst`/`v_*_fst` (design decision §3.4).
* `w3a_exists_params`: the body of `G11_exists_params` :8705 verbatim with `G11_ParamsSw.gu3_triangle_compact /
  gu3_disc_convex / gu3_triangle_sub_interior_disc` (copied), `RProof.gu3_edgeSegment_isClosed` (C-free, qualified),
  `C.clear_edge` (the skeleton's) and `w3bc_exists_small` (= `gu3_exists_small` :8650 over `G11_ConfigSw`, placed
  just before it in `SM.Link`).

Every proof compiled at the first attempt; no reassessment case arose.

## 3. Notes for the DE prover / the assembler

* The DE range 4918–8630 contains further C-free helpers (e.g. `gu6_sv_fst_eq`, `gu6_sv_strand`, `gu6_svisit_ext`,
  `gu6_overStrand_eq`, `gu6_over_under_of_pos/neg`, `gu6_det_ne_zero_single`, `gu6_xPair_ne_of_not_mem`,
  `gu6_riii_build`, `gu6_riii_of_strands`, the `GU6Single*` sections); the same `#check`-classification recipe
  (scratch `CheckTypes2.out`, 481 declarations) applies.  If the DE copy is appended INSIDE `section W3A1Copy`
  it can extend the `open RProof.G11_Params (…)` list; my names it must not redefine: `w3bc_over_under_pos`,
  `w3bc_over_under_neg`, `w3bc_det_pos_iff_of_sign_eq` (in `G11_ParamsSw`), `w3bc_exists_small` (in `SM.Link`).
* `gu6_htrans` (the only consumer of `trans`) is outside my range and was not copied; `riii` must become
  `w3a_riii_param` as the skeleton states.
* Skeleton line numbers in `W3_SKELETON_REPORT.md` §2 are offset (its "207" is line 199, "412" is 404, …); anchor
  on names, not lines.
* Per-check compile time of the 5.2k-line file is 44 s on this pod (not the feared minutes); a merged BC+DE file
  (~9k lines) should stay well under 2 min.
