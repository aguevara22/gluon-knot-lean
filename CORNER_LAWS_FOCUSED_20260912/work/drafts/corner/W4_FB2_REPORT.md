# W4_FB2 report — unit FB2: F's BLACK BOX 2 `s7f_exists_twoNewbornTerm` closed

Written 2026-09-19 07:45 UTC / 03:45am ET by the wave-4 FB2 executor (Claude Code, session
resumed after the 2026-09-18 ~01:55 UTC container OOM restart; author decision D-AUTH-20260919 read
from `/workspace/repos/lean/author_response.md` and already on record in `work/AUTHOR_NOTES.md`).
Row 110 `thm:C-S7`, OPEN_ITEMS_20260916 §A-08.

## 1. Result

| item | value |
|---|---|
| deliverable | `work/drafts/corner/W4_FB2.lean` (12,978 lines; sha256 `54c923c0f6a20cd37eb4009a06caff5c3ebde7feff8cded705a02d6de4b33813`) |
| base | `cp` of `work/drafts/corner/W3_Assembled.lean` (8,958 lines; sha256 `109050d9…83736f`) |
| closed | `s7f_exists_twoNewbornTerm` (W3_Assembled decl 5388, sorry 5405) — body is now `exact s7fb_exists_twoNewbornTerm hn g h h₁ h₂` |
| inserted | ONE block, lines **5381–9400** (4,020 lines), immediately before the box's docstring, inside `section S7FSectorSplit`; 150 top-level `s7fb_` declarations + 54 members of `namespace s7fb_BigonTransport` (204 declarations) |
| compile | `lake env lean ../drafts/corner/W4_FB2.lean` from `work/lean`: **0 errors**, 33.9 s (`full_compile6.log`) |
| `declaration uses sorry` | 12 → **11** (lines 4437, 4519, 4844, 5371, 9745, 10992, 11038, 12620, 12640, 12659, 12926) |
| `grep -c sorry` | 20 → **19** |
| new black boxes | **none** — no `s7fb_` Prop was left with `sorry`; all inputs came from the file's own proved material and the library |
| frozen text | lines 1–5380 of W4_FB2 are byte-identical to lines 1–5380 of W3_Assembled; lines 9401–12978 are byte-identical to W3_Assembled 5381–8958 except the one body line `sorry` → `exact …`. The five frozen declarations, `s7_sliding_law_at`, `s7_bigon_law_at`, and every existing statement/name/docstring are unchanged. |
| remaining warnings | 4 unused-section-variable linter notes (`hT` auto-included in `s7fb_BigonTransport.owner_yl`, `.markTurn_first`, `.markTurn_second`, `.triangle_sum`); cosmetic, left because `omit hT in` breaks the dot-notation call sites |
| `work/lean` | untouched (rule); `lake build` never run |

Axiom footprint (`#print axioms` on a scratch copy, `scratchpad/fb2/axioms2.log`; the file has
not changed structurally since, only `hlt` was dropped from `owner_yl`):

- `SM.s7f_exists_twoNewbornTerm`, `SM.s7fb_exists_twoNewbornTerm`, `SM.s7fb_twoNewbornTerm_at`,
  `SM.s7fb_BigonTransport.coef_first` : `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`
  — the three registered literature interfaces enter only through the library's coefficient
  transport (`s7d_cornerCoefficient_eq_of_cut` / `corner_values_i`), as in every other consumer of them; **no `sorryAx`**.
- `SM.s7fb_bigonTransport_of`, `SM.s7fb_carrierRotation_first/second`,
  `SM.s7fb_BigonTransport.carrierWeight_first`, `.carrierWeight_M`, `.cornerList_first_rotated`,
  `SM.s7fb_ya_lt_xa_of_not_interlaces`, `SM.s7fb_exists_detRadius` : `[propext, Classical.choice, Quot.sound]`.
- `SM.s7f_sector_split`, `SM.s7f_exists_law_residual` still carry `sorryAx` — through boxes 1 and 3
  (`s7f_exists_bigonSplit`, `s7f_exists_ineligible_transport`), not through box 2.

## 2. What is proved (the `ε = 0` two-newborn row, sm-4:434-447)

Setting: `h : g.BigonAt M a`, `h₁ h₂` generic halves, side `b = s7f_side g M a`, newborn-side polygon
`Q = P₂(t) = g.curve (g.sideTime b t)`, centre `Pc = g.center` with `s7a2_IntervalLocal` data
`(r, η, δ, hloc)` from `s7a2_exists_intervalLocal` (contact parameter `Pc M = edgePoint Pc a r`,
windows of half-width `η`, `0 < r < 1`, `4η < r`, `4η < 1 − r`). Newborns `x = {a, M−1}`,
`y = {a, M}`; visits `x_a, y_a` on edge `a`, `x_ℓ` on edge `M−1`, `y_ℓ` on edge `M`.

**Part A (`S7FBSide`, 5392–5708) — geometry of the newborn side.** Leg lemmas (`s7fb_leg_false/true`),
affectedness of the two newborns and non-affectedness of everything else, `s7fb_visit_cases`,
persistence (`s7fb_persistent_of_edge_a/_pred/_M`), window positions (`s7fb_xa_near`, `s7fb_ya_near`
on `E_a` within `η` of `r`; `s7fb_xl_param`, `s7fb_yl_param` within `η` of `1`, resp. `0`), the three
successor facts `nextMark (inr x_ℓ) = inl M`, `nextMark (inl M) = inr y_ℓ`, `nextMark (inr y_a) = inr x_a`
(the last under `p(y_a) < p(x_a)`), and the **dichotomy** `s7fb_ya_lt_xa_of_not_interlaces`:
`¬ Interlaces x y → p(y_a) < p(x_a)` on `E_a` (the interlacing test reduces to the order of the two
newborn visits on the shared edge; the other two visits lie on consecutive edges `M−1`, `M` around the
vertex `μ_M`). These make the contact triangle `x_a → μ_M → y_ℓ → x_a` of sm-4:437-441.

**Part B1 (`S7FBMap`, 5720–6090) — the bigon mark map.** `def s7fb_mark : (Mark F₁ ⊕ Mark F₂) ⊕ Unit → Mark Q`
sends first-half marks through `s7b_slidingMark … x_ℓ`, second-half marks likewise, the two copies of
`μ_M` to `inl M`, and the unit to `inr x_a`; computation rules, `s7fb_mark_inl_eq`
(= `swap (inl M) (inr y_a) ∘ s7b_slidingMark`), injectivity, the range description
(`s7fb_inr_mem_range_iff`, `s7fb_M_mem_range`, `s7fb_xa_not_mem_range`, `s7fb_yl_not_mem_range`),
transit windows (`s7fb_transit_of`, `s7fb_transit_window`), the half-mark pullbacks `s7fb_qmark₁/₂`
with edge/parameter rules and the two cut facts `s7fb_qmark₂_param_zero`, `s7fb_qmark₁_param_cut`.

**Part B2 (`S7FBReturn`, 6092–6638) — the first-return law** (U_S7B §2.4's "not started" item, now
proved): `s7fb_reach_first/second` (RET's `s7r_Transit` engine: `s7r_reach_of_transit`,
`s7r_hit_of_transit`, `s7r_step_of_reach`, `s7r_between_next_vertex`, …), `s7fb_step_first/second`
(the successor of an image mark is the image of the half successor, except at the vertex `μ_M`),
`s7fb_succ_M`, `s7fb_succ_yl`, `s7fb_succ_xa`, `s7fb_step_unit`, `s7fb_hit`, then
`structure s7fb_BigonTransport S₁ S₂ : Prop` (fields `x_mem y_mem first_pre second_pre img ret`) and
`s7fb_bigonTransport_of` producing it below the radius from `¬ Interlaces x y` and the split.

**Part C (`S7FBTransport`, 6645–7067) — the component correspondence.** For
`T = insert x (insert y (joinSupport S₁ S₂))`: `componentEquiv : Component hn hQ T ≃ (C₁ ⊕ C₂) ⊕ Unit`
via `s7fb_unitCycleEquiv` and `s7b_ReturnTransport`'s `cycleEquiv`; owner lemmas
(`componentEquiv_owner_first/second/M/firstVisit/secondVisit/ya/xl`, `owner_yl`, `owner_xa`,
`owner_eq_M_iff`, `symm_inr_unit`); the unit component is the triangle: `carrierCrossings_M_eq_empty`,
`carrierCrossingCount_M = 0`, `mem_cornerList_M_iff`, `ccpCornerCount_M = 3`; the other components carry
exactly the images of the half carriers (`carrierCrossings_eq_img_first/second`,
`isTrueCorner_first/second`, `not_isTrueCorner_of_off_image`).

**Part D1 (`S7FBCorners`, 7077–7667) — corner lists transfer as rotations.** `s7fb_cycle_next_congr`
(DecidableEq-instance bridge), orbit lemmas `pow_first/second`, `not_corner_of_orbit_first/second`,
`cornerMark_succ_first/second` via `ccp_corner_chain`/`ccpCornerMark_add_one`,
`mem_cornerList_first_iff/second_iff`, `cornerList_first_rotated/second_rotated`, and
`cornerMark_first_shift/second_shift : k = k₁ ∧ ∃ s, ∀ j, ccpCornerMark T q j = ι (ccpCornerMark S₁ q₁ (j + s))`.

**Part D2 (`S7FBTurns` 7675–7903, `S7FBWeights` 7905–8257) — turns and weights.** Determinant algebra
(`s7fb_det_sub_right/self`, `s7fb_sign_sub_of_opposite`, `s7fb_sign_smul_pos`, `s7fb_chi_eq`,
`s7fb_turn_eq`), `s7fb_triple_ne_contactSupport`, `s7fb_crossingSign_centre`, edge-vector relations
(`s7fb_PcM_eq`, `s7fb_edge_first_smul/second_smul`), turn persistence `s7fb_turn_first/second`,
the two newborn mark turns `s7fb_markTurn_ya = turn F₁ 0`, `s7fb_markTurn_xl = turn F₂ 0`,
`markTurn_first/second`, `carrierWeight_first/second` (image components have the half weights),
`triangle_sum`, `turn_M`, and `carrierWeight_M = −(chi Q a (a+1) M : ℤ)` (three corners of turn `−s₀`).

**Part E (`S7FBFamilyPrelim` 8267–8530, `S7FBFamily` 8532–8905, `S7FBRotation` 8907–9009) — rotation
numbers.** A continuity argument (`s7fb_continuous_det`, `s7fb_continuousAt_edgeParameter`,
`s7fb_det_aM_center`, `s7fb_det_M1a_center`) gives a second radius `δ'` (`s7fb_exists_detRadius`)
below which the four newborn-edge determinants keep the centre's signs; with it an A2-style corner
family (`s7fb_Kind g M a b sp m`, `s7fb_kind_visit_det`, `s7fb_kind_corner_det`, `s7fb_kind_psi_ne_zero`,
`s7fb_family_edge/psi_ne_zero/psi_continuousAt/psi_pos/regular/continuousOn`) is a regular family of
corner polygons through the centre, so `rotationNumber_family_constant` + `Reindexed` give
`s7fb_carrierRotation_first/second`: the image components have the half rotation numbers; the triangle
has `|rot| = 1` via `corner_values_i` (unconditional).

**Part F (`S7FBCoefficients`, 9014–9122) — coefficients.** `coef_first/second` transport
`cornerCoefficient` to the halves through the cut form (`s7d_cornerCoefficient_eq_of_cut`,
`s7q_cutFirst_of/_cutSecond_of` from ROT, `s7fb_qmark₁_param_cut`, `s7fb_qmark₂_param_zero`);
the triangle's coefficient is `1` (`corner_values_i`: `d = 0`, `c = 1`).

**Germ inputs and assembly (`S7FBGermInputs` 9127–9218, `S7FBAssembly` 9222–9399).** `s7fb_hord`
(the visit-order data of `VertexLocalData` on `P₂(t)`), `s7fb_sign_const_center`, `s7fb_hside`,
`s7fb_neg_chi : −(chi P₂ a (a+1) M : ℤ) = s7f_dirSign g M a * (g.contactSign M a : ℤ)` (from
`g.vertex_contact_signs`); `s7fb_twoNewbornTerm_at` computes `s7e_term` of `T ∪ {x, y}` as a product
over `(C₁ ⊕ C₂) ⊕ Unit` (`s7c_map_univ_eq_of_equiv`, `s7c_carrierWeight_eq_sel`,
`s7c_carrierWeight_triangle`, `Fintype.prod_unique`) and regroups it as
`(δ_dir · s) · term(T₁) · term(T₂)`; `s7fb_exists_twoNewbornTerm` takes `δ'' = min δ δ'` and
restates the box verbatim.

## 3. Method notes

- Everything is built on the library engines already accepted or drafted for row 110 (RET's transit
  engine, U_S7B's `s7b_ReturnTransport`/`cycleEquiv`, U_S7C's carrier-weight selectors, U_S7D's
  coefficient transport, W2_S7A2's interval-local data and corner family, W2_S7E's vertex/leg API,
  ROT's cut lemmas). No library statement was restated; the DecidableEq-instance mismatch between
  library `Cycle.next` results (`Classical.propDecidable`) and this file's `RProof.instDecidableEqCrossing`
  is bridged once by `s7fb_cycle_next_congr`.
- Reassessment discipline (D-AUTH-20260919 §2): no lemma failed twice on substance; every failure
  was mechanical (section-variable `include`/`omit`, dependent `rw` on `getElem`/`Cycle.next`/`Sigma`,
  `pow_succ` vs `pow_succ'`, `Fintype.prod_unique` target, `SignType.sign 0` not rfl, `Fact (1 < k)`
  for `−1 ≠ 0` in `ZMod k`) and fixed on the next attempt; no method audit was triggered.
- Scratch compilation used a prelude olean of the draft prefix plus per-part oleans (`scratchpad/fb2/`,
  wrapper `lean.sh` with the toolchain binary and an extended `LEAN_PATH`), ~10–17 s per piece; the
  full draft compiles in ~26–34 s. Backups `W4_FB2_backup_v1/v2/v3.lean` are in the scratch dir.

## 4. Remaining sorries in `W4_FB2.lean` (unchanged from W3_Assembled, 11 declarations)

`s7q_box_ret` (4437), `s7q_box_carriers` (4519), `s7_sliding_law_at` (4844), `s7f_exists_bigonSplit`
(5371, F box 1), `s7f_exists_ineligible_transport` (9745, F box 3), `s7s_clear_local` (10992),
`s7s_wallTriangleData_of_bigon` (11038), `s7z_F_exists` (12620), `s7z_returned_of_FSector` (12640),
`s7z_oneNewborn_exists` (12659), `s7_bigon_law_at` (12926). Next units per W3_ASSEMBLY_REPORT §7 and
OPEN_ITEMS §A-02: F boxes 1 and 3, then the S-unit and Z-unit boxes, then the ROT boxes.

## 5. For consumers

`s7f_exists_twoNewbornTerm` now has the same statement and a real proof; K's `s7f_sector_split` /
`s7f_exists_law_residual` pick it up with no change. The `s7fb_` material stays in the draft until the
row's port (`work/drafts/corner/port/`), where `port_stmt_check.py` applies; nothing under `work/lean`
was touched. The intermediate `s7fb_BigonTransport` structure and `componentEquiv` may be useful for
the one-newborn row (`s7z_oneNewborn_exists`) — the same mark map with only one newborn.
