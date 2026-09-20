# R174_WALL_REPORT — unit WALL (row 174, Wave 2): `gsc_Ledger` items 2 and 3

Prover (subagent), 2026-09-15 ≈ 23:40 UTC / 7:40pm ET.  File: `work/drafts/moves/R174_WALL.lean`
(= `Site_174.lean`, byte-identical for its 2941 lines, + 2458 appended lines, prefix `r174w_`).
Inputs read: Site_174_REPORT.md (§3 the stated `s174_hrec_prop`, §5 the remaining obligations),
U_R174_REPORT.md §4 items 2–3, RProof/RALedgers.lean (`gsc_WallData`, `gsc_Ledger`, `gsc_moves`,
`gsc_wall_of_endpoint`, `gsc_wallData_of_endpoint`), RProof/X1Rows3.lean (`GT_Wall`, `GT_Good`,
`GT_carrierEquiv`, `GT_owner_transport`, `GT_geoCarrierCrossings_eq_of_good`, `GT_groupedPoly_eq_homfly`,
`GT_homfly_wall_gen`, `GT_Endpoint` and its namespace, `GT_owner_eq_of_adjacent`, `GT_succ_of_adjacent`,
`GT_cyc_*`), RProof/X1Rows2.lean (`EXT_homfly_wall`), CV/X1.lean (`groupedPoly`, `groupedWrithe`, `carrierR`,
`slot`, `Omega1`, `groupedWrithe_eq_card_geoCarrierCrossings`), CV/Carriers.lean (`weight`),
SM/FlatCarriersDefs.lean (`geoSmoothingSuccessor`, `geoOwner`, corner lists, `cornerSelector`),
SM/GeoCornerPolygon.lean (`geoCornerPolygon_turn_vertex/visit`, `_edge_smul`, `_edge_pred_smul`),
SM/GeoCarrierCount.lean (the insertion layer: `geoSmoothingSuccessor_insert_child_data`,
`geoOwner_insert_iff_of_unaffected`, `geoMarkList_filter_left/right_iff`, `geoIndependent_inheritsMarkOrder`,
`geoIndependent_remaining_pair_owners`, `geo_selected_visits_separated`), SM/GeoCarrierCrossings.lean
(`geo_neighbor_visit_owners_ne`), CV/Rotation.lean, CV/UniformRot.lean, CV/TurnLift.lean (`two_pi_mul_rot`),
SM/RegularPairs.lean (`principalAngle`), SM/AngleScaling.lean.

## 0. Deliverables and checks

| item | result |
|---|---|
| `R174_WALL.lean` | 5399 lines = `Site_174.lean` (2941, `head -n 2941 … \| diff` prints nothing) + the appended section "R174 WALL" (lines 2942–5399, 2458 lines, 201 declarations) |
| compile `cd work/lean && lake env lean ../drafts/moves/R174_WALL.lean` | exit 0, **0 errors**, ≈ 29 s; warnings: exactly the skeleton's **33** `declaration uses sorry` + its one cosmetic `<;>` linter note (line 566).  **No new `sorry`**: `grep -c sorry` = 34 before and after |
| black boxes consumed | **none** — no stated Prop with `sorry` was needed; HREC's outputs were not required (the retained-crossing correspondence is proved here directly from `GT_owner_transport`) |
| `#print axioms` | `r174w_writhe_wall_ledger`, `r174w_retained_qAB`, `r174w_weight_AB`, `r174w_weight_C`, `r174w_carrierR_add`, `r174w_hsigma`, `r174w_split_exists`, `r174w_sigma_vs_crossingSign`, `r174w_angle_add_of_pos`: `propext, Classical.choice, Quot.sound` only.  `r174w_omega_wall_ledger`, `r174w_omega_C`: `+ SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (through `homfly`/`CV.gausscode_polynomial` in `EXT_homfly_wall` / `GT_homfly_wall_gen`), the accepted footprint of every `Ω₁` transport in the library.  No `sorryAx` anywhere in `r174w_` |
| frozen material | nothing above line 2941 changed; nothing under `work/lean` written |
| reassessment rule | never triggered on a lemma (two proof-search detours are recorded in §6: the kernel trap and the classical `insert` instance) |

## 1. What is PROVED

### 1a. Item 2 — the wall (`omega_wall`, `writhe_wall`), section `R174W_Wall` (lines 2974–3312)

Setting: `hn`, `hG hG' : CV.Generic`, `D : GT_Endpoint hG.cg hG'.cg hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃`,
`hSm : Q ∪ {m} ∈ Ind`, `hSm' : transportSupport hs (Q ∪ {m}) ∈ Ind`; `τ := (gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ`
(= `GT_carrierEquiv (gsc_wall_of_endpoint …)`, `r174w_τ_eq : … = r174w_τ hG hG' D hSm hSm'` is `rfl`).
`qAB := geoOwner hG.cg (Q ∪ {m}) (Sum.inr D.x₂)` (`r174w_qAB`), the carrier of the `ℓ₂`-visits of `x, w`
(`r174w_owner_x₂_eq_w₂`: adjacent unselected visits, `GT_owner_eq_of_adjacent`).

* `r174w_x'_mem_retained`, `r174w_w'_mem_retained`: `x', w' ∈ geoCarrierCrossings hG'.cg S' (τ qAB)` — the site
  inputs `hx', hw'` of `s174_site`/`s174_fulltwist_of_hrec` (Site_174_REPORT §5, first row, estimated 0.4–0.8k;
  actual ≈ 60 lines).  Proof: `x₂` and `w₂` are GOOD marks of the centre row (`r174w_good_x₂/w₂`: their only
  reversed partner is each other and neither is selected), so `GT_owner_transport` carries their ownership to
  `τ qAB`; on the one-edge side `x', w' ∈ U(S')` (`r174w_x'_mem_U'`: `compl` turns the `x–m` interlacing off,
  `toggle` + `Q_avail` keep `Q` off), so both visits are on one carrier (`CV.owner_eq_of_mem_U`).
* `r174w_x'_retained_iff / r174w_w'_retained_iff`: `x' ∈ retained(τ q) ↔ q = qAB`.
* `r174w_retained_eq_of_ne (q) (hq : q ≠ qAB) : retained' (τ q) = (retained q).map (crossingTransport hs)`
  (outside crossings have good visits, `r174w_retained_iff_of_outside`; `x, w, m` are retained by nobody on `P`
  — `x, w ∉ U(Q ∪ {m})` as neighbours of `m`, `r174w_x_not_mem_U` — and `m'` by nobody on `P'`).
* **`r174w_retained_qAB : retained' (τ qAB) = insert x' (insert w' ((retained qAB).map transport))`.**
* **`writhe_wall`**: `r174w_writhe_wall_ledger (qAB) (hqAB : geoOwner … (Sum.inr D.x₂) = qAB) :
  CV.groupedWrithe hG' (W.τ qAB) = CV.groupedWrithe hG qAB + 2` (`groupedWrithe_eq_card_geoCarrierCrossings`,
  `card_insert_of_notMem` twice, `card_map`).
* **`omega_wall`**: `r174w_omega_wall_ledger (qAB) (hqAB) : ∀ q, q ≠ qAB → CV.Omega1 hn hG' hSm' (W.τ q) = CV.Omega1 hn hG hSm q`:
  `groupedWrithe` by the card, `carrierR` by `GT_carrierR_eq` (the realised `W.carrierR_wall`), `groupedPoly` by
  `r174w_groupedPoly_wall` = `GT_groupedPoly_eq_homfly` twice + `EXT_homfly_wall` (retained sets correspond;
  key orders of visits of retained crossings are carried by `W.key_lt` since a retained crossing of a centre-row
  carrier is an outside crossing, `r174w_outside_of_retained`, hence never a reversed pair; divide signs by
  `D.sign_eq`).

### 1b. Item 3 — the corner-sign and rotation ledger (`weight_C`, `weight_AB`, `carrierR_add`, `hσ`), plus `omega_C`

Section `R174W_Ledger` (lines 5236–5395), on the ledger's own supports `Q ∪ {m}`, `Q ∪ {x, w}`
(`hSm`, `hSxw : … ∈ Ind` as in `gsc_moves`), with the canonical-branch hypothesis
`hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃` exactly as `gsc_moves` states it (`D.sgn` supplies the third).
The carriers are named by the visits they own:

| ledger carrier | definition here | hypothesis form in the theorems |
|---|---|---|
| `qAB` (centre row) | `geoOwner hG.cg (Q ∪ {m}) (inr D.x₂)` | `hqAB : qAB = geoOwner … (inr D.x₂)` |
| `qC` (centre row) | `geoOwner hG.cg (Q ∪ {m}) (inr D.x₁)` | `hqC : qC = geoOwner … (inr D.x₁)` |
| `qA` (pair row) | `geoOwner hG.cg (Q ∪ {x, w}) (inr D.m₁)` | `hqA` |
| `qB` (pair row) | `geoOwner hG.cg (Q ∪ {x, w}) (inr D.m₃)` | `hqB` |
| `qC'` (pair row) | `r174w_qC' hG hG' D := geoOwner … (inr (visitTwin (r174w_sp hG hG' D).xA))` — the carrier through the visit of `x` NOT carried by `A` | characterised by `r174w_qC'_owns` (it carries a visit of `x` and a visit of `w`) and `r174w_qC'_unique` (any carrier of the pair row carrying a visit of `x` and one of `w` is `qC'`); `r174w_qA_ne_qC'`, `r174w_qB_ne_qC'`, `r174w_qA_ne_qB'`, `r174w_qAB_ne_qC` |
| `σ` | `r174w_sigma hG hG' D : ℤ := −τ(mAB)`, minus the turn sign of the smoothing corner of `AB` | `r174w_hsigma : σ = 1 ∨ σ = −1`; `r174w_sigma_vs_crossingSign` (§2) |

* **`weight_AB` (GSC (5))**: `r174w_weight_AB hn hG hG' D hsgn qAB hqAB qA qB hqA hqB :
  wt(Q∪{x,w}) qA * wt(Q∪{x,w}) qB = r174w_sigma hG hG' D * wt(Q∪{m}) qAB`.
* **`weight_C` (GSC (5))**: `r174w_weight_C hn hG hG' D hsgn qC hqC : wt(Q∪{x,w}) (r174w_qC' hG hG' D) = −r174w_sigma hG hG' D * wt(Q∪{m}) qC`.
* **`carrierR_add` (GSC (8))**: `r174w_carrierR_add hn hG hG' D hsgn hSm hSxw qAB hqAB qA qB hqA hqB :
  wt(Q∪{m}) qAB ≠ 0 → CV.carrierR hn hG hSm qAB = CV.carrierR hn hG hSxw qA + CV.carrierR hn hG hSxw qB`.
* **`omega_C`** (bonus, U_R174 §4 item 3's fourth field): `r174w_omega_C hn hG hG' D hsgn hSm hSxw qC hqC :
  CV.Omega1 hn hG hSxw (r174w_qC' hG hG' D) = CV.Omega1 hn hG hSm qC`, from
  `r174w_retained_C` (`C` and `C'` retain the SAME crossings), `r174w_carrierR_C` (`R(C') = R(C)`) and
  `r174w_groupedPoly_C` (`GT_homfly_wall_gen` with the identity on visits).
* The intermediate `r174w_retained_C : retained(Q∪{x,w}) qC' = retained(Q∪{m}) qC` is also what item 5/6
  (smoothing, writhe count) will want for the spectator/`C` side.

How (5) and (8) are proved — the corner-mark reformulation (section `R174W_Corners`, lines 3428–3791):

* `r174w_tau P : Mark P → SignType` (a vertex `i ↦ turn P i`; a visit `v ↦ crossingSign P v.edge (twin v).edge`),
  `r174w_theta P : Mark P → ℝ` (the corresponding principal angles), `r174w_corners hP S q` (the owned true corners).
  `r174w_turn_eq`: `turn (geoCornerPolygon q) k = tau (geoCornerMark q k)` (`geoCornerPolygon_turn_vertex/visit`);
  `r174w_principalTurn_eq`: `principalTurn (geoCornerPolygon q) k = theta (geoCornerMark q k)`
  (`geoCornerPolygon_edge_pred_smul`, `_edge_smul`, `principalAngle_smul`); `r174w_corners_eq_image`,
  `r174w_card_corners` (the corner marks are the image of `geoCornerMark`, injective).
* `r174w_weight_eq : CV.weight hP S q = r174w_F P (corners q)` with
  `F C := if ∀ a ∈ C, τ a = −1 then 1 else if ∀ a ∈ C, τ a = 1 then (−1)^|C| else 0`;
  `r174w_two_pi_rot : 2π · rot(cornerPolygon q) = Σ_{a ∈ corners q} θ a` (`two_pi_mul_rot`, lem:turnlift (ii));
  `r174w_uniform_of_weight_ne_zero`, `r174w_rot_of_uniform` (`uniformrot.pos_ge_one/neg_le_neg_one`).
* `r174w_F_split`: for disjoint `C₁ C₂` and marks `a ∉ C₁`, `b ∉ C₂`, `c ∉ C₁ ∪ C₂` with `τ a = τ b = τ c = τ ≠ 0`:
  `F(insert a C₁) · F(insert b C₂) = −τ · F(insert c (C₁ ∪ C₂))`; `r174w_F_two`:
  `F(insert a (insert b C)) = −τ · F(insert c C)`.  `r174w_rot_add`, `r174w_rot_eq_two`: the rotations add /
  agree when the corner sets split so and `θ a + θ b = θ c`; `r174w_carrierR_add_of`: `R` adds under a nonzero
  selector (both children inherit the uniform sign, so `|rot A + rot B| = |rot A| + |rot B|`).
* `r174w_angle_add_of_pos/neg` (section `R174W_Angle`): `∠(u₁,u₂) + ∠(u₂,u₃) = ∠(u₁,u₃)` when the three
  determinants have one sign (`Complex.arg_mul_coe_angle` + the bounds pin the integer).
  `r174w_angle_identities` specialises to the triangle `u₁ u₂ u₃` under `hsgn`/`D.sgn`.
* `r174w_turn_data`: the three smoothing corners of `A`, `B`, `AB` turn the same way `τ`, those of `C`, `C'` the
  opposite way, `θ(xA) + θ(wB) = θ(mAB)`, `θ(xC) + θ(wC) = θ(mC)`, `τ ≠ 0`.

The carrier structure behind it (section `R174W_Config`, lines 3883–5231) — this is the content U_R174 §4 item 1
called "the geo-layer insert/remove step applied twice", done here for the visits' carriers and the corner sets:

* `r174w_child`: the geo layer's `geoSmoothingSuccessor_insert_child_data` read on mark keys: inserting `v.1` into
  `T` (inherited order, both visits on one carrier) splits that carrier into `{v} ∪ (twin v, v)`-arc and
  `{twin v} ∪ (v, twin v)`-arc (`cycBetween` on `geoMarkKey`), all other carriers unchanged
  (`r174w_unaffected_w` = `geoOwner_insert_iff_of_unaffected`).  Applied to `Q → Q ∪ {m}` (`r174w_split_m`),
  `Q → Q ∪ {x}` (`r174w_split_x`), `Q ∪ {x} → Q ∪ {x, w}` (`r174w_split_w`); the partition lemmas
  `r174w_part_m/x/w` (every mark of the parent lands in one child) and `r174w_onZ_of_*` (children lie in the parent).
* The six local visits lie on one carrier `q₀` of `Q` (`r174w_ownerQ_*`: pair owners of `x, w, m ∈ U(Q)` and
  adjacency), the separations (`r174w_sep_*`: selected twins and neighbours' visits are on different carriers).
* **The orientation case analysis** (`r174w_split_exists : Nonempty (r174w_Split D)`), from
  `GT_succ_of_adjacent D.adj1`: either `x₁` immediately precedes `m₁` on `ℓ₁` (**case B**, the printed word
  `a b A a c B b c C`, `r174w_split_caseB`) or `m₁` immediately precedes `x₁` (**case A**, the reversed traversal,
  `r174w_split_caseA`).  In each case the other two adjacency orientations are FORCED by ownership
  (`σ₀ x₂ = w₂` and `σ₀ m₃ = w₃` in case B; `σ₀ w₂ = x₂`, `σ₀ w₃ = m₃` in case A) — no sign condition needed —
  and the record `r174w_Split` collects: `xA, wB, mAB` (the visits of `x, w, m` carried by `A, B, AB`; case B:
  `x₂, w₃, m₃`; case A: `x₁, w₂, m₁`), the memberships `oA oB oC' oAB oC`, the three regular containments
  `P1 P2 P3` (every nonspecial mark of `A` or `B` lies on `AB`, every nonspecial mark of `C'` on `C`), the
  on-`q₀` facts and the trichotomy `triZ`.  The arc inclusions are real-number `cycBetween` arithmetic
  (section `R174W_Cyc`: `r174w_cyc_trans_left/right`, `_split`, `_asymm`, `_mid`, `_wrap`), fed by the arc facts
  the split lemmas return from OWNERSHIP equalities (e.g. `owner_m x₂ = owner_m m₃ ⟹ cycBetween m₁ x₂ m₃`) and
  the "no mark strictly between" facts of the adjacent pairs (`r174w_no_between` from
  `geoMarkSuccessor_prev_no_mark_between`).
* Corner sets: `r174w_corners_A/B/Cp/AB/C` (each is its special visit(s) inserted into its nonspecial corners),
  `r174w_reg_AB` (the nonspecial corners of `AB` are those of `A` and `B`, `r174w_reg_disj`), `r174w_reg_C`
  (those of `C` are those of `C'`); `r174w_corner_iff` (for a nonspecial mark, corner of `Q ∪ {m}` ⟺ corner of
  `Q ∪ {x, w}`).

## 2. The canonical sign — a fidelity finding (not a defect of the frozen ledger)

Both traversal orientations occur with the SAME `crossingSign ℓ₁ ℓ₂` (the point reflection of the triangle
through `m` preserves every edge direction and every determinant but reverses the order of the two crossings on
each edge); `GT_Endpoint` is symmetric under it, and the sign condition `hsgn` ties only the three orientations
to each other (`s174_order`).  In the printed orientation (case B) the smoothing corners of `A, B, AB` turn with
sign `−crossingSign ℓ₁ ℓ₂` and (5) reads `wt(A) wt(B) = crossingSign ℓ₁ ℓ₂ · wt(AB)`; in the reversed one they
turn with sign `+crossingSign ℓ₁ ℓ₂` and the identity holds with the NEGATED sign
(`F(insert a C₁) F(insert b C₂) = −τ F(insert c (C₁ ∪ C₂))` with `τ` the common corner turn: `r174w_F_split`).
So **`wt(A) wt(B) = crossingSign ℓ₁ ℓ₂ · wt(AB)` is false in the reversed orientation whenever the weights are
nonzero**, and the same for `wt(C') = −crossingSign ℓ₁ ℓ₂ · wt(C)`.

This is NOT a defect of `gsc_Ledger`: its `σ` is a free field (`σ : ℤ`, `hσ : σ = 1 ∨ σ = −1`; the RA
consumption `gsc_omega_jump`/`gsc_couple_of_ledger` uses only `hσ`, `weight_C`, `weight_AB` and `σ·σ = 1`).
The realiser must choose `σ := r174w_sigma hG hG' D = −τ(mAB)`, which is `crossingSign ℓ₁ ℓ₂` exactly when `AB`
carries `m₃` (case B) and `−crossingSign ℓ₁ ℓ₂` when it carries `m₁` (`r174w_sigma_vs_crossingSign`).  The
docstrings of `gsc_Ledger` ("`σ = ±1` is the canonical sign (1)") and `gsc_moves` ("all three strand-determinant
signs equal `σ`") read `σ` as `crossingSign ℓ₁ ℓ₂`; that reading is right for the printed word only.  No frozen
statement needs editing (rule 4 did not have to be invoked); the AUTHOR_NOTES entry for row 174 should record
the orientation dependence.  `gsc_sigma_of_endpoint` (about `crossingSign ℓ₁ ℓ₂ = ±1`) stays true but is not the
right `hσ` witness; `r174w_hsigma` is.

## 3. Wiring into `gsc_Ledger` (for the realiser of `gsc_moves`)

With `D`, `hsgn`, `hSm hSxw hSm'` as in `gsc_moves`, `W := gsc_wallData_of_endpoint hn hG hG' D hSm hSm'`, and the
carrier choices of the table in §1b (`qAB := geoOwner … (inr D.x₂)`, `qC := geoOwner … (inr D.x₁)`,
`qA := geoOwner … (inr D.m₁)`, `qB := geoOwner … (inr D.m₃)`, `qC' := r174w_qC' hG hG' D`, `σ := r174w_sigma hG hG' D`):

| field | theorem (all `hqAB/hqC/hqA/hqB := rfl`) |
|---|---|
| `hσ` | `r174w_hsigma hG hG' D hsgn` |
| `hCAB : qC ≠ qAB` | `(r174w_qAB_ne_qC hG hG' D).symm` |
| `hC'A, hC'B, hAB` | `(r174w_qA_ne_qC' …).symm`, `(r174w_qB_ne_qC' …).symm`, `r174w_qA_ne_qB' …` |
| `omega_wall` | `r174w_omega_wall_ledger hn hG hG' D hSm hSm' qAB rfl` |
| `writhe_wall` | `r174w_writhe_wall_ledger hn hG hG' D hSm hSm' qAB rfl` |
| `omega_C` | `r174w_omega_C hn hG hG' D hsgn hSm hSxw qC rfl` |
| `weight_C` | `r174w_weight_C hn hG hG' D hsgn qC rfl` |
| `weight_AB` | `r174w_weight_AB hn hG hG' D hsgn qAB rfl qA qB rfl rfl` |
| `carrierR_add` | `r174w_carrierR_add hn hG hG' D hsgn hSm hSxw qAB rfl qA qB rfl rfl` |
| `qx`, `fulltwist` | `s174_fulltwist_of_hrec … qAB (W.τ qAB) (r174w_x'_mem_retained …) (r174w_w'_mem_retained …) hrec` — the site inputs `hx', hw'` of Site_174_REPORT §5 are now PROVED (`W.τ` is `r174w_τ` by `r174w_τ_eq`, `rfl`) |
| `ρ`, `ρ_AB`, `ρ_C`, `spectator_*` (item 1) | not this unit; the structure is available: `r174w_Split` + `r174w_unaffected_w`/`geoOwner_insert_iff_of_unaffected` give every carrier of `Q` other than `q₀` as a common carrier of both rows (item 1's spectators); `r174w_retained_C` and `r174w_owner_C_iff` give the `C ↦ C'` clause |
| `D₀`, `i j ℓ`, `smoothing`, `writhe_count` (items 4–6) | not this unit |

If item 1 chooses different but equal carriers (e.g. `qAB := geoOwner … (inr D.w₂)`), rewrite with
`r174w_owner_x₂_eq_w₂` (Part A) / the `r174w_ownerm_*`, `r174w_qC'_unique` lemmas.

## 4. Black boxes, unproved, false-as-stated

* Black boxes consumed: **none** (no `sorry` added, no stated Prop of another unit used).
* Unproved within this unit's scope: nothing.  Not attempted (other units): item 1's bijection `ρ` and spectator
  clauses, items 4–6, `s174_hrec_prop`.
* False as stated: nothing in `gsc_Ledger`/`gsc_moves`; only the docstring reading of `σ` (§2).

## 5. Sizes

Part A (item 2) 340 lines; corner-mark reformulation + selector/rotation algebra 470; cyclic-order helpers 85;
configuration facts, child data, partition 330; the two orientation cases 355; carriers, corner sets, turn data,
exports 450; ledger-form theorems 160; headers 70.  Total 2458 lines (the task estimated 1.4–2.2k for items 2–3;
item 1's "carrier structure" was needed as scaffolding and is included).  Compile ≈ 29 s for the whole file.

## 6. Pitfalls met (for the 176/HREC provers)

1. **Kernel trap: `Subtype.val` over two different `Finset` predicates.**  Proving `(ψ v).1 = v.1` by `rfl` for
   `ψ : {v // v.1 ∈ retained S q} ≃ {v // v.1 ∈ retained S' q'}` makes the KERNEL (not the elaborator) time out:
   with equal head `Subtype.val` it first compares the implicit predicates and attempts to unfold the two
   `geoCarrierCrossings`-memberships (`Finset.filter`, `Multiset`, decidability) before falling back.  Cure:
   keep the value equation explicit — `obtain ⟨ψ, hψ'⟩ : ∃ ψ, ∀ z, ψ z = ⟨z.1, _⟩ := ⟨Equiv.subtypeEquivRight _, fun _ => rfl⟩`,
   `e z := (congrArg Subtype.val (hψ' z)).trans (Subtype.coe_mk _ _)`, then `rw [e]` in the side goals
   (`r174w_groupedPoly_C`).  With the heartbeat limit raised the `rfl` version does check — in 8 minutes.
2. **The geo layer's `insert` is classical.**  `SM/GeoCarrierCount.lean` has `attribute [local instance]
   Classical.propDecidable`, so its `insert v.1 S` carries `fun a b => Classical.propDecidable (a = b)`, while
   `RProof` provides `instDecidableEqCrossing`; `rw [hL z]` against the child data fails silently on the instance
   ("argument `c` … expected `{s // IsCrossing P s}`").  Cure: `@[instance_reducible] def r174w_decEqCrossing :=
   fun a b => Classical.propDecidable (a = b)` with `attribute [local instance high] r174w_decEqCrossing` in every
   section that mentions `insert`/`Finset (Mark P)`; NOT in the ledger-facing section, whose `Q ∪ {m}` must keep
   `RProof`'s instance to match `gsc_Ledger`.  The bridge between the two worlds is a support variable with an
   equation (`(Sm) (hSm_eq : Sm = insert m Q)`, `subst` inside), instantiated at `Q ∪ {m}` with the proof
   `by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto` written INLINE (a
   standalone lemma stating the equation elaborates the wrong instance).
3. `geoOwner`-equalities are the right currency: every arc fact (`cycBetween (key m₁) (key x₂) (key m₃)` etc.)
   comes for free from an ownership equality through the child-data biconditionals — no explicit derivation of
   the six-visit cyclic order from interlacing was needed, and the case split is decided by ownership too.
4. `intro hw; exact f … hw` versus `exact f …` (partial application) for a `≠ 0 →` goal: the former cost a
   deterministic timeout at `whnf` (`r174w_carrierR_add`), the latter is instant.
5. `rcases` on `GT_succ_of_adjacent`'s disjunction into a Type-valued `def` is refused; produce
   `Nonempty (r174w_Split D)` and `Classical.choice` it once (`r174w_sp`).
6. Section-variable inclusion: a theorem whose statement does not mention `D`/`sp`/`hn` needs `include … in`;
   `omit [NeZero n] in` for pure `Finset` facts; the auto-included `hG hG'` are explicit arguments of every
   Part A lemma (`r174w_x_not_mem_Sm hG hG' D`).
7. `if_pos/if_neg` are deprecated here (`ite_eq_left/ite_eq_right`); `push_neg` → `push Not`; for `SignType` case
   splits rewrite the constructor to the literal first (`e2 : SignType.pos = 1 := rfl`) and then decide the
   literal inequalities; `((−s : SignType) : ℤ) = −(s : ℤ)` is `cases s <;> rfl` (`r174w_signType_cast_neg`).
