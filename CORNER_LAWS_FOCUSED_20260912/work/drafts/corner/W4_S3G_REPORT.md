# W4_S3G_REPORT — wave 4, unit S3G (prefix `s7g_`, serving ROT's box `s7q_box_carriers` = Prop S3 `w3_SlidingCarriers`), 2026-09-19 07:20 UTC / 3:20am ET

File: `work/drafts/corner/W4_S3G.lean` = `W3_Assembled.lean` (8,958 lines) + ONE inserted `s7g_` block (lines 4508-7644, **3,137
lines, 162 declarations**: 152 theorems, 9 defs/abbrevs, 1 structure; every top-level name carries the prefix `s7g_`, the 21
unprefixed ones live in `namespace s7g_Delete`) placed inside `section S7QBoxes` immediately BEFORE the docstring of the sorried
box `s7q_box_carriers`, and ONE changed line: the box's body `sorry` → `exact s7g_box_carriers_literal hn g h h₁ h₂` (line 7682).
`diff W3_Assembled.lean W4_S3G.lean` = `4507a4508,7644` + `4545c7682` — a pure insertion plus the one permitted body replacement;
the five frozen declarations (`s7_sliding_law_at`, `s7_bigon_law_at`, `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7`) and every
other existing statement, name and docstring are byte-identical. 12,095 lines, sha256 `486cbc91463cab4e…`.
No imports added; nothing written under `work/lean`.

**Check (official)**: `cd work/lean && lake env lean ../drafts/corner/W4_S3G.lean` — **0 errors, 0 warnings other than
`declaration uses sorry`**, exit 0, ~30 s (load ≈ 5). **`declaration uses sorry`: 12 → 11** — the eleven remaining are exactly the
other units' bodies and the two leaves: `s7q_box_ret` 4437, `s7_sliding_law_at` 7981, `s7f_exists_bigonSplit` 8508,
`s7f_exists_twoNewbornTerm` 8525, `s7f_exists_ineligible_transport` 8862, `s7s_clear_local` 10109,
`s7s_wallTriangleData_of_bigon` 10155, `s7z_F_exists` 11737, `s7z_returned_of_FSector` 11757, `s7z_oneNewborn_exists` 11776,
`s7_bigon_law_at` 12043.  `grep -c sorry`: **20 → 19** (the box's body; the 8 prose mentions of W3_ASSEMBLY_REPORT §4 are
unchanged, the new block adds none).  `python3 work/drafts/corner/tools/stmt_check.py W4_S3G.lean`: **4/49**, identical to the
result on `W3_Assembled.lean` (the checker expects the assembled statements file; unchanged by this unit).
**Axioms** (`#print axioms`, scratch copy): every `s7g_` theorem checked = `[propext, Classical.choice, Quot.sound]` — no
literature axiom, no `sorryAx`; **`s7q_box_carriers` = `[propext, Classical.choice, Quot.sound]`**, hence
**`w3_SlidingCarriers_of_box : w3_SlidingCarriers … := s7q_box_carriers …` is now sorry-free: Prop S3 is PROVED**.
`s7q_box_rows`, `thm_C_S7` still carry `sorryAx` (through `s7q_box_ret` / the leaves only).
Clash scan: the library's `s7g_` names (U110-G: `s7g_coeffAt_*`, `s7g_cornerCoefficient_extraction`, `s7g_cornerHomfly_skein`,
`s7g_extraction_*`, `s7g_skein_at_positive`, `s7g_switch_*`, `s7g_value_of_ri`) are disjoint from this unit's; the compile is the
definitive check (no duplicate name in the file: `sort | uniq -d` empty).

## 0. In one paragraph

The S3 geometry (ROT (a)-(f), W3_ROT_REPORT §6, OPEN_ITEMS §A-05) is PROVED for BOTH transports, and the frozen box
`s7q_box_carriers` is CLOSED AS STATED.  Route (the corrected route of W3_ROT_REPORT §3.2): (a) the sign-level ORDERED corner
correspondence is derived from the first-return law `ret` alone — a carrier of the side polygon has the `ι`-images of the corners
of its half carrier in the same cyclic order plus at most ONE extra off-image corner (`s7g_corner_correspondence`, its bijective
and extra-corner forms); (b) `hbit` is the constancy of the persistent crossing signs through the wall (`s7g_hbit_first/_second`);
(c) `hr` in two steps: the EXACT deletion of the extra corner inside the side polygon (`s7g_Delete.rotation_eq` with the
half-plane identities `s7g_delete_angle_a/_b`, α = β = 1 — the merged edge is the SUM of the two edges at the deleted corner)
and the PERTURBATION to the half through the LABEL FAMILY `s7g_family` (the half carrier's corner marks read on `g.curve u` through
`t`-independent labels, continuous at the centre and equal to the half's corner polygon there; `rotationNumber_locally_constant`
plus turn constancy `s7g_eventually_polygon`, made uniform over the finitely many half carriers by `Filter.eventually_all`,
`s7g_exists_radius`); (d) the turn signs of all corners by the same eventual statement; (e)/(f) the contact-sign memberships and
`τ = turn g.center M ≠ 0` through the contact tests and `g.SlidingAt`'s opposite-sides clause (`s7g_contactSign_mem`,
`s7g_tau_ne_zero`).  On the leg-`M` side the accepted `s7b_SlidingTransport` never exists (RET's rule-4 finding, now formalised for
both pivots, `s7g_B_no_transport_vl` / `s7g_B_no_transport_va`), so the box's leg-`M` clauses are vacuous and the box holds
literally; the leaf-relevant content on that side is delivered on RET's corrected `s7r_SlidingTransport'` as the primed copy
`s7g_CarrierData'` (`s7g_carriers_legM`).  The leaf `s7_sliding_law_at` is NOT closed: its other input S1 `w3_SlidingRet` is false
as stated (OPEN_ITEMS §A-03) and the S1' restatement is unit S1P's.

## 1. What is proved (all `s7g_`, sorry-free, standard axioms; `{n} [NeZero n]` and, where used, the ambient `(hn) (g) {M a} (h)`
of `section S7QBoxes`)

### 1.A Chains and the ordered corner correspondence (sections `S7GChain` 4531-4599, `S7GCorners` 4601-4820)
* `s7g_chain_compare` (two chains from one mark: A to a corner through non-corners, B to a corner through non-corners-or-`c` ⇒
  equal length and equal ends, or A shorter and its end is `c`), `s7g_chain_iterate` (the transport of an `r`-fold `ρ₁`-chain
  through a first-return mark map: `K ≥ r` steps, intermediates in the skipped set `X` or images of `ρ₁`-intermediates).
* **`s7g_corner_correspondence`** (4620): for `Q`, `S` a decomposition, `q`; a half-type polygon `L` (`3 ≤ k`, generic), `S₁` a
  decomposition, `q₁`; `ι : Mark L → Mark Q` injective, `X` a set of marks disjoint from the image, `c` a mark, with
  `hXc` (the only true corner in `X` owned by `q` is `c`), `hcorner` (`IsTrueCorner S (ι m) ↔ IsTrueCorner S₁ m`), `howner`
  (`owner (ι m) = q ↔ owner m = q₁`), `hstep` (the first-return law: `ρ^k (ι m) = ι (ρ₁ m)`, `0 < k`, intermediates in `X`),
  `hcover` (every corner of `q` is in `X` or an image): **∃ `e : ZMod k₁ → ZMod k` injective with `c'_{e j} = ι c_j`, and for each
  `j` either `e (j+1) = e j + 1` or (`c ∉ range ι`, `c'_{e j + 1} = c`, `e (j+1) = e j + 2`), covering every corner other than `c`**.
  Proof: `ccp_corner_chain` on both polygons + `s7g_chain_iterate` + `s7g_chain_compare` twice (the second comparison from `c`
  onwards); `ccpCornerCount_ge_three` excludes `e j + 2 = e j + 1`.
* `s7g_corner_correspondence_bij` (no off-image corner owned by `q` ⇒ `e` bijective with `e (j+1) = e j + 1`),
  `s7g_corner_correspondence_extra` (`c ∈ X` a corner owned by `q` ⇒ `s7g_Delete`-data: one gap at the unique `j₀` with
  `c'_{e j₀ + 1} = c`, `e (j₀+1) = e j₀ + 2`, `e j ≠ e j₀ + 1`, every index is an `e j` or `e j₀ + 1`).

### 1.B Relabelling and the exact deletion (section `S7GRelabel` 4821-5183)
* `s7g_relabel_edge/_edge_pred/_principalTurn/_turn` (`P ∘ e` along a successor-preserving `e`), **`s7g_relabel_rotation_bij`**,
  **`s7g_relabel_turns_bij`** (a cyclic-order-preserving bijection of index sets leaves `rotationNumber` and `s7c_turns` unchanged).
* **`structure s7g_Delete e j₀ : Prop`** (`inj`, `succ` off `j₀`, `gap : e (j₀+1) = e j₀ + 2`, `ne : e j ≠ e j₀ + 1`, `cover`);
  `edge_j₀ : edge (P ∘ e) j₀ = edge P (e j₀) + edge P (e j₀ + 1)` (the merged edge is the SUM, α = β = 1), `principalTurn_of_ne`,
  `turn_of_ne`, `principalTurn_j₀/_j₀_succ`, `turn_j₀/_j₀_succ`, `sum_eq` (the summation bookkeeping), **`rotation_eq`**
  (`rotationNumber P = rotationNumber (P ∘ e)` from the angle identity `∠(e',r) + ∠(r,u) + ∠(u,w) = ∠(e',r+u) + ∠(r+u,w)`),
  `turns_core` (`s7c_turns P + {t' j₀, t' (j₀+1)} = s7c_turns (P ∘ e) + {t (e j₀), t (e j₀+1), t (e (j₀+1))}`),
  **`turns_eq_a`** (orientation (a): `s7c_turns P = s7c_turns (P ∘ e) + {turn P (e (j₀+1))}`), **`turns_eq_b`** (orientation (b):
  `… + {turn P (e j₀)}`).
* **`s7g_delete_angle_a`** (`u`, `w` on one side of `r`; `r + u` on the same side of `e'` and `w` as `r`: the leg-`(M−1)` deletion
  of `v_a`) and **`s7g_delete_angle_b`** (`e'`, `r` on one side of `u`; `r + u` on the same side of `e'`, `w` as `u`: the leg-`M`
  deletion of `v_ℓ`), both from ROT's `s7q_principalAngle_add_of_side/_side'` and `s7q_two_turn_perturb`.

### 1.C Labels, the label family, eventual constancy (sections `S7GLabels` 5184-5307, `S7GCentre` 5309-5599)
* `s7g_Label n := ZMod n ⊕ ZMod n × ZMod n`, `s7g_labelPoint R` (vertex `↦ R i`; pair `↦ edgePoint R e (edgeParameter R e f)`),
  `s7g_GoodLabel`, `s7g_labelPoint_continuousAt` (good labels are continuous in the germ parameter at the centre),
  `s7g_eventually_sign` (a continuous real function nonzero at a point has eventually constant sign), `s7g_eventually_turn`,
  **`s7g_eventually_polygon`** (at a regular polygon with nonzero turns: eventually equal rotation number AND all turn signs).
* **`def s7g_family g hk hL S₁ q₁ lab u : LabelledTuple k₁`** (`j ↦ labelPoint (g.curve u) (lab c_j)`), `s7g_family_zero` (at the
  centre it IS `ccpCornerPolygon q₁` when the labels read the half's own points), `s7g_family_continuousAt`,
  **`s7g_family_eventually`** (near the centre: rotation number and all turns of the half's corner polygon).
* The centre: `s7g_det_a_M`, `s7g_det_a_pred`, `s7g_sign_det_a_M : sgn det(edge a, edge M) = chi a (a+1) (M+1)`,
  `s7g_sign_det_a_pred : sgn det(edge a, edge (M−1)) = −chi a (a+1) (M−1)`; `s7g_edge_firstHalf/_secondHalf` (each half edge is a
  positive multiple of the centre's edge with the image label), `s7g_crossingSign_firstHalf/_secondHalf`; the four label maps
  **`s7g_lab₁`, `s7g_lab₂`** (for `s7b_slidingMark (s7e_vl hc)`: `λ₂`'s vertex `0 ↦ (M−1, a)`) and **`s7g_lab₁'`, `s7g_lab₂'`** (for
  `s7r_slidingMark' (s7e_va hc)`: `λ₁`'s vertex `0 ↦ (a, M)`), their centre identities `s7g_lab*_center` (visits by
  `contact_pair_data.point_eq` + `s7b_crossingPoint_*HalfCrossing`; the contact labels by `edgeParameters_of_intersection`,
  `s7g_cramer_pred_a/_a_M`) and goodness `s7g_lab*_good`.

### 1.D The side polygon (sections `S7GSideCommon` 5600-5808, `S7GSideA` 5809-6249, `S7GSideB` 6250-6704)
* `s7g_turn_firstHalf/_secondHalf` (half vertex turns off `0` = centre turns at the image label), **`s7g_markTurn_first`**
  (`s7b_slidingMark`, `λ₁`, marks ≠ vertex `0`) and **`s7g_markTurn_second'`** (`s7r_slidingMark'`, `λ₂`, marks ≠ vertex `0`) from the
  two sign-constancy inputs `hvturn : turn Q i = turn P i`, `hcsgn` (persistent crossing signs); **`s7g_hbit_first/_second`**
  (= the `hbit` clauses of `s7q_CarrierData`, for EVERY carried visit); `s7g_vertex_cases` (every vertex label is a first-half
  label or a nonzero second-half label — `contact_root_cases` is not in the import closure); the point identities
  `s7g_point_first/_first'/_second/_second'` (the side polygon's point of a carried mark is its label's point);
  `s7g_next_corner_of_succ` (a corner whose successor is a corner is followed by it); `s7g_turns_eq_of_turn_eq`.
* Side A (leg `M−1`, `hT : s7b_SlidingTransport … S S₁ S₂ (s7e_vl hc)`, `hSimg`): `s7g_A_vertex_mem`, **`s7g_A_offImage_corner`**
  (the only off-image true corner is `v_a`), `s7g_A_corner_first/_second`, `s7g_A_owner_first/_second`, `s7g_A_step_first/_second`
  (from `hT.ret.step`), `s7g_A_cover_first/_second`, `s7g_A_va_owner : owner v_a = owner μ_M` (`s7r_succ_va`), `s7g_A_va_component`;
  the correspondences **`s7g_A_corr_first_bij`** (`q₁ ≠ owner (inl 0)`), **`s7g_A_corr_second_bij`**, **`s7g_A_corr_first_extra`**
  (`s7g_Delete` data with `c'_{e j₀ + 1} = v_a`); `s7g_A_poly_first/_second` (`ccpCornerPolygon q ∘ e` = the label polygon);
  **`s7g_A_first_bij`, `s7g_A_second_bij`** (equal rotation and weight) and **`s7g_A_first_extra`** (6146): the contact carrier —
  the corner after `v_a` is `μ_M` (`s7r_succ_va`), so `c_{j₀+1} = inl 0`; the three edges at `prev`, `v_a`, `μ_M` are positive
  multiples of `edge a`, `edge (M−1)`, `edge M` (`ccpCornerPolygon_edge`, `ccpOutSlot_selected`, `ccpCornerPolygon_outEdge_eq_inEdge`);
  (a1) the sliding signs at the side, (a2) `turn (poly ∘ e) j₀ = turn poly (e j₀)` by `s7g_markTurn_first`, (a3)
  `turn (poly ∘ e) (j₀+1) = turn poly (e j₀ + 1)` = `turn λ₁ 0 = sgn det(edge a, edge M) = crossingSign Q a (M−1)`; then
  `s7g_delete_angle_a` + `s7g_Delete.rotation_eq` + `turns_eq_a`: `carrierRotation q₁ = carrierRotation q` and
  `carrierWeight q = s7c_sel (s7c_turns (poly q₁) + {turn P M})`.
* Side B (leg `M`, `hT : s7r_SlidingTransport' … (s7e_va hc)`): the mirror list `s7g_B_*` with the extra corner `v_ℓ` AFTER `μ_M`
  (`s7g_B_vl_owner` by `s7e_owner_inl_eq_next` + `s7r_nextMark_M`), **`s7g_B_corr_second_extra`**, **`s7g_B_second_extra`** (6594) with
  (b1)-(b3) and `s7g_delete_angle_b` + `turns_eq_b`, refined at `λ₂`'s contact carrier by `turn P M`.

### 1.E The germ (sections `S7GGerm` 6705-7105, `S7GGermBox` 7106-7317, `S7GNoTransport` 7318-7388, `S7GGermLiteral`
7390-7427, `S7GNoTransportVa` 7429-7540, `S7GGermLiteralBox` 7542-7643)
* `s7g_chi_ne_zero`, `s7g_triple_succ_ne/_pred_ne`, `s7g_chi_succ_ne_zero/_pred_ne_zero`, **`s7g_sliding_signs`**
  (`sgn det(edge a, edge (M−1)) = sgn det(edge a, edge M) ≠ 0` at the centre: `g.SlidingAt`'s clause
  `chi a (a+1) (M−1) ≠ chi a (a+1) (M+1)` with both nonzero), `s7g_contact_dets`, `s7g_turn_side` (vertex turns are the centre's on
  the whole interval: `ChirotopesOutsideZerosAgree` + `contactSupport_ne_turnSupport`).
* **`s7g_exists_radius`** (6821): `∃ δ > 0, ∀ |u| < δ`: persistent crossing signs are the centre's; the two contact determinants have
  the centre's signs; for EVERY decomposition and carrier of each half and BOTH label maps of that half, the label family at `u` has
  the half's rotation number and turns.  (`Filter.eventually_all` over the finite index types, `g.eventually_center_iff_radius`.)
* **`def s7g_CarrierData' hn g h hQ hQC h₁ h₂ hT a₀ m₀ τ`** — the verbatim copy of `s7q_CarrierData` on `s7r_SlidingTransport'`
  (its `componentEquiv`), the S1P/S3′ interface for the leg-`M` side.
* **`s7g_carriers_legpred`** (6947): `∃ δ > 0, ∀ t < δ, ∀ b, ∀ (hc : IsCrossing (side b) {a, contactLeg false M}) S (hS) (hsplit :
  s7b_PivotSplit … (s7e_va hc).1) S₁ S₂ hS₁ hS₂ (hT : s7b_SlidingTransport … S S₁ S₂ (s7e_vl hc)),
  s7q_CarrierData hn g h (s7a_sideGeneric g b) (s7e_hQC hn g h t b) h₁ h₂ hT (s7q_contactPoint … S₁ S₂ true)
  (s7q_contactTurns … S₁ S₂ true) (turn g.center M)`.
* **`s7g_carriers_legM`** (7028): the same with `{a, contactLeg true M}`, `hT : s7r_SlidingTransport' … (s7e_va hc)`, conclusion
  `s7g_CarrierData' … hT (s7q_contactPoint … false) (s7q_contactTurns … false) (turn g.center M)`.
* **`s7g_tau_ne_zero : turn g.center M ≠ 0`**; `s7g_turn_firstHalf_zero/_secondHalf_zero`, `s7g_turn_zero_mem_first/_second`;
  **`s7g_contactSign_eq`** (`g.contactSign M a = if s7e_leg g M a then −chi a (a+1) (M+1) else chi a (a+1) (M+1)`, from
  `vertexEdge_contact_tests` at one side parameter and `vertex_contact_signs`); **`s7g_contactSign_mem`** (the two membership clauses
  of the box with `first = !s7e_leg g M a`).
* **`s7g_box_carriers'`** (7229): the box with the leg-`M` side on the primed transport (both sides, `first = !s7e_leg`,
  `τ = turn g.center M`; the clause for the transport a side does NOT carry is vacuous by `s7e_pattern`).
* **`s7g_A_no_transport_va`**, **`s7g_B_no_transport_vl`** (cheap: `f v_a = μ_M` resp. `f μ_M = v_ℓ` is an image mark at step one)
  and **`s7g_B_no_transport_va`** (7466; RET's chain argument: `μ_M → v_ℓ → nextMark v_a`, then `s7r_reach_from_va'`; the two mark
  maps at `v_a` have the same image, so the first image mark met is an `inr`-image while `ret.step` demands the `inl`-image
  `ι (inl (ρ₁ (inl 0)))`).  **`s7g_box_clause_legpred`** (7395): the leg-`(M−1)` clause of the box in its literal form
  `∀ vm hT, vm.1 = x → …` (the `v_a` pivot is empty).
* **`s7g_box_carriers_literal`** (7549): the EXACT statement of `s7q_box_carriers`, proved (`first := !s7e_leg g M a`,
  `τ := turn g.center M`; per side: the literal leg-`(M−1)` clause, or vacuity from the two non-existence lemmas).

## 2. The box (closed) and its clauses

`s7q_box_carriers` (7656) now has the body `exact s7g_box_carriers_literal hn g h h₁ h₂` (its docstring and statement untouched).
Clauses of the box (W3_ROT_REPORT §2 item 4) and what closes them:

| clause | closed by |
|---|---|
| `τ ≠ 0`, `first`, the radius | `s7g_tau_ne_zero`; `first = !s7e_leg g M a`; `δ = min` of the radii of `s7g_box_clause_legpred` and `s7a2_exists_intervalLocal` |
| `g.contactSign M a ∈ s7q_contactTurns … first`, `−g.contactSign M a ∈ s7q_contactTurns … (!first)` | `s7g_contactSign_mem` |
| side `false`, `∀ vm hT, vm.1 = x₋ → s7q_CarrierData … (contactPoint first) …` | `s7e_leg = false`: `s7g_box_clause_legpred` at `b = false`; `s7e_leg = true`: VACUOUS (`s7g_B_no_transport_va`, `s7g_B_no_transport_vl`) |
| side `true`, `∀ vm hT, vm.1 = x₊ → s7q_CarrierData … (contactPoint (!first)) …` | `s7e_leg = true`: `s7g_box_clause_legpred` at `b = true`; `s7e_leg = false`: VACUOUS |

`s7q_CarrierData`'s four clauses on the side carrying `{a, M−1}` (per row, per `hT`): `hbit` for `λ₁`/`λ₂` carriers =
`s7g_hbit_first/_second`; `hr` = `s7g_A_first_bij/.1`, `s7g_A_first_extra/.1`, `s7g_A_second_bij/.1`; the weights off `a₀` =
`s7g_A_first_bij/.2`, `s7g_A_second_bij/.2`; the refined weight `sel(m₀ + {τ})` at `a₀ = inl (owner (inl 0))` = `s7g_A_first_extra/.2`.
The leg-`M` side's content in the SAME four clauses on the corrected transport: `s7g_carriers_legM` (`s7g_B_*`).

**Consequence for the leaf**: `w3_SlidingCarriers_of_box` (Prop S3) is sorry-free.  `w3_s7_sliding_law_at_of₂ hret hcar` now needs only
S1 `w3_SlidingRet`, which is FALSE as stated (W3_RET_REPORT §2, OPEN_ITEMS §A-03) — the leaf waits on unit S1P's restatement S1′ and
the re-typing of `w3_box_rows_of` / `w3_s7_sliding_law_at_of₂`; for the leg-`M` side S1P should consume `s7g_carriers_legM` /
`s7g_CarrierData'` (a copy of ROT's `s7q_rowData_of_carrierData` on `s7r_SlidingTransport'.componentEquiv` is needed there; not
part of this unit).  The frozen leaf `s7_sliding_law_at` keeps its `sorry`.

## 3. Black boxes and intermediates from other units

None.  No `s7g_` Prop is stated with `sorry`; nothing was needed from S1P, F, SITE, BLOCK, J or K.  Consumed (all PROVED in the
assembled file or the library): RET's `s7r_SlidingTransport'`, `s7r_slidingMark'` and its computation rules,
`s7r_slidingMark'_injective`, `s7r_inr_mem_range_iff/_iff'`, `s7r_va_not_mem_range`, `s7r_vl_not_mem_range'`, `s7r_succ_va`,
`s7r_succ_vl'`, `s7r_nextMark_M`, `s7r_reach_from_va'`, `s7r_nextMark_shape`, `s7r_img_of_decomposition`, `s7r_huniq/_huniq'`,
`s7r_hord`, `s7r_hside`; ROT's `s7q_principalAngle_add_of_side/_side'`, `s7q_two_turn_perturb`, `s7q_CarrierData`,
`s7q_contactPoint/_contactTurns`, `s7q_Split`; the library's `ccp_*` corner-polygon toolkit, `s7b_*` (U110-B), `s7a2_*` (A2 germ
data), `s7e_*` (E: `s7e_pattern`, `s7e_hQC`, `s7e_hw`, `s7e_va/_vl`, `s7e_owner_inl_eq_next`), `s7c_carrierWeight_eq_sel`,
`s7c_map_univ_eq_of_equiv`, `s7d_positiveOverBit_eq_of_crossingSign`, `s7i_principalTurn_eq_of_pos_smul`,
`rotationNumber_locally_constant`, `continuousAt_edgeParameter_of_det`, `contact_pair_data`, `edgeParameters_of_intersection`,
`vertexEdge_contact_tests`, `vertex_contact_signs`, `g.eventually_center_iff_radius`.

## 4. Defects / readings (rule 4) — nothing false found

* Nothing in the frozen statement or the box is false.  ROT's second defect note (§3.2, "the exact fields hold only on the same
  side polygon") is confirmed and is exactly the shape used: the exact structures `s7q_CornerMerge/_CornerPerturb` are NOT
  instantiated across the wall; the exact step is `s7g_Delete` on `Q(t)` (with α = β = 1, simpler than `s7q_principal_delete`'s
  `α r + β u`), the wall crossing is the eventual statement on the label family.
* ROT's `s7q_principal_delete` (hypotheses `sign det(e,r) = sign det(e,d)`, `sign det(d,w) = sign det(r,u)`) is the orientation-(a)
  identity; orientation (b) (leg `M`, the short edge FIRST) needs the mirrored hypotheses — `s7g_delete_angle_b`.  Both are
  derived from ROT's half-plane lemmas; `s7q_principal_delete` itself is not used.
* `contact_root_cases` (SM/ContactRootPartition.lean) is not reachable from the frozen imports; re-proved as `s7g_vertex_cases`.
* The `if first then … else …` of `s7q_contactPoint/_contactTurns` at the literals `true`/`false` is accepted by `show`/defeq.

## 5. Reassessment audit (the 2-attempts / 60-min rule)

No lemma needed two failed proof attempts; every section compiled after one or two rounds of local fixes (typos, argument
orders, `include`/`omit` lists).  Method changes made deliberately before coding, not after failure: (i) the corner correspondence
is built from the successor structure (`ccp_corner_chain` + `ret`) instead of A2's sorted-mark-list route
(`s7a_ccpCornerList_map`), because the sliding mark map is not key-monotone; (ii) the deletion is done on the side polygon with
`e : ZMod k₁ → ZMod k` (`P ∘ e`) instead of a `(k−1)`-tuple, avoiding `ZMod (k−1)` arithmetic; (iii) the uniform radius is an
`∀ᶠ` at the centre over the finite type of (decomposition, half carrier) pairs — no `∀ |u| < δ` path-regularity of the
deleted polygon is needed (the point where ROT expected 300-500 lines).  Cost: ≈ 90 minutes of wall clock (05:45-07:20 UTC),
one compile per section on a ~4,500-line context (`ctx.lean` = the assembled prefix through `s7q_CarrierData`; 25-40 s each),
final full compile 30 s.

## 6. Pitfalls met (v4.34.0-rc2 pin)

* Section-variable inclusion: a Prop variable used only in a proof must be `include`d (`include hD hk₁ in`), `include … in` must
  precede the docstring; `omit [NeZero k] in` errors when the statement references the instance.
* `neg_ne_zero` / `neg_neg` need a subtraction monoid — not `SignType`; use `cases x <;> simp_all` (`s7g_sign_neg_ne_zero`) or
  `revert x y; decide` (`s7g_signType_eq_neg_of_ne`, `s7g_signType_mul_eq_neg_one`).
* `Finset.add_sum_erase` must be given its function explicitly (`(fun j => f (e j))`) or the `?f (j₀+1)` pattern does not unify.
* `rw [visit_crossing_val_eq_pair v]` under `Finset.image` fails (motive not type-correct: `v.2` depends on `v.1`); use `congrArg`.
* `h.1.2.1 : g.pointZeros = …` is only DEFINITIONALLY `pointZeroTriples g.center = …`: annotate the `have` before `rw`.
* RET's `s7r_slidingMark'_inr_inl/_inr_inr` are stated at `s7e_va hc`; for a general `va` use `show` with the definitional unfolding.
* Identifiers cannot contain `₊`/`₋`.
* `ContinuousAt.eventually` does not exist; use `Filter.Tendsto.eventually` (`ContinuousAt` is `Tendsto`).
* `s7r_img_of_decomposition hn hQ hsep hm hQC h₁ h₂ S x hsplit hS hx` — `S` and `x` are explicit and precede the proofs; pass `x`
  explicitly when the proof of `hsplit` rewrites it.

## 7. Reproduce

`cd work/lean && lake env lean ../drafts/corner/W4_S3G.lean` (~30 s idle; several minutes under load): expected output exactly
eleven `declaration uses sorry` lines (§0).  `diff W3_Assembled.lean W4_S3G.lean | grep -E '^[0-9]'` → `4507a4508,7644` and
`4545c7682`.  `#print axioms` on a scratch copy with the names of §1 appended after `end SM` (`SM.s7q_box_carriers`,
`SM.w3_SlidingCarriers_of_box`, …).  Timeline: 05:45 UTC resume and reading; 06:15 sections A-B compile; 06:30 C; 06:45 D/DA;
06:55 DB; 07:05 E/E2/F; 07:12 G and the box closed; 07:20 report.
