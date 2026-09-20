# W6_ROT_REPORT — wave-6 unit ROT (prefix `w6r_`): the rotation fields of BR's two turn boxes, 2026-09-19 (under D-AUTH-20260919, no bound)

File: **`work/drafts/corner/W6_ROT.lean`** (25,768 lines) = `W5_Assembled.lean` (25,237 lines) + ONE `w6r_` block of 530 lines
(20 declarations) inserted inside `section W4Bigon` immediately before the docstring of `w4_box_returnedRows`:
`diff W5_Assembled.lean W6_ROT.lean | grep "^[0-9]"` = **`25096a25097,25627`** (one insertion, NO body replaced — the GLUE
assembler fills BR's boxes).  **Compile** (`cd work/lean && lake env lean ../drafts/corner/W6_ROT.lean`): **0 errors, 0 warnings
other than exactly 11 `declaration uses sorry`** = W5's 10 (4439, 18055, 18496, 23881, 24278, 24287, 24304, 25071, 25090, the leaf
now at 25716) + **25595 `w6r_box_centreCorners`** (this unit's one consumed black box).  `grep -c sorry`: 22 → 23 (the one new
sorry body; no prose mention added).  `tools/stmt_check.py --base W3_Skeleton.lean` 5/5 PASS; `tail -n 43` identical to
`W3_Skeleton.lean`; `tools/clash_scan.py`: `duplicates_in_assembled: []`, `full_name_clashes: {}` (1385 new decls, all 20 of
this unit `UNPREFIXED:w6r_*` = top-level names with the unit prefix).  Nothing written under `work/lean`; `lake build` never run.

## 0. In one paragraph

**Both rotation identities are PROVED, sorry-free, in the exact shapes of `w5b_InterlacingTurnData.rotation` and
`w5b_NoninterlacingTurnData.rotation`** (BR's binders `hn g h h₁ h₂ t T₀ hloc ht hT₀ hS₁ hS₂`, hypotheses `hI` and
`hW : carrierWeight … (w5b_qL …) ≠ 0`), from TWO per-`(t, T₀)` Props: ROW's `w5r_CornerData` (consumed by CALLING
`w5r_box_corners`, not restated) and this unit's `w6r_CentreCornerData` (the corner correspondence read on the centre in
PRINCIPAL-TURN form — the one black box, `w6r_box_centreCorners`, radius form over `w4_EligDec`, sorried).
`#print axioms w6r_rotation_interlacing` = `#print axioms w6r_rotation_noninterlacing` = `[propext, Classical.choice, Quot.sound]`.
The radius form `w6r_exists_rotation` (both identities under `wt(q_L) ≠ 0`, below the radii of `w5r_box_corners` and
`w6r_box_centreCorners`) carries `sorryAx` through exactly those two boxes.  **Why a second box** (§3): U110-I's ledger
(`s7i_interlacing_absolute` / `s7i_noninterlacing_absolute`) needs the correspondence `e` to preserve PRINCIPAL turns (angles), and
`w5r_CornerData` delivers only SignType turns on `P₂(t)` — the angle statement is not derivable from it; the task's route
("with the correspondence `e, he` from `w5r_box_corners` in principalTurn form") presupposed a shape the declared box does not
have.  What IS derived here without any new box: `L*`'s regularity, `rot(L*) = rot(q_H)`, the EXACT equality of SignType turns
`turn L* i = turn (ccp q_H) i` for every corner (`w6r_turn_Lstar`, sign constancy of the original corner determinant along A2's
family), the sign patterns of all three polygons, the identification of the excluded corners with the halves' dissents at `ε = 0`,
the weight and rotation transfers `q_L ↔ q_H`, and the SPLICE LEMMA `w6r_principalTurn_of_splice` — the bridge from a mark-level
description of the merged corner lists (points, cyclic order, the splice on `E_a`) to the principal-turn form, packaged for
`L*, ccp L₁, ccp L₂` as `w6r_centreCornerData_of_splice` (contact points discharged by `w6r_Lstar_contact`, `w6r_ccp_L₁_contact`,
`w6r_ccp_L₂_contact`), so that W6-COR / the GLUE can close `w6r_box_centreCorners` from the corner-list merge it builds anyway.

## 1. Deliverables — exact statements (lines in `W6_ROT.lean`; `q_H := w5r_qH` (`≡ w5b_qH`), `q_L := w5b_qL … hloc ht`
(`= (s7fc_e …).symm q_H`), `L₁ := w5r_L₁` (`≡ w5b_L₁`), `L₂ := w5r_L₂`, `ccp := ccpCornerPolygon`, `s₀ := w5r_sgn g M a`)

| line | declaration | statement | status |
|---|---|---|---|
| 25495 | **`w6r_rotation_interlacing hn g h h₁ h₂ t T₀ hloc ht hT₀ hS₁ hS₂ (hI : s7f_Interlacing hn h t) (hW : carrierWeight hn hP₀ T₀ q_L ≠ 0) (hCC : w5r_CornerData hn g h h₁ h₂ t T₀) (hL : w6r_CentreCornerData hn g h h₁ h₂ t T₀)`** | `|carrierRotationInt hn hP₀ T₀ q_L| = |carrierRotationInt … h₁ _ (w5b_L₁ …)| + |carrierRotationInt … h₂ _ (w5b_L₂ …)|` — byte-for-byte BR's `rotation` field at `ε = 1` | **PROVED**, standard axioms only |
| 25530 | **`w6r_rotation_noninterlacing … (hI : ¬ s7f_Interlacing hn h t) hW hCC hL`** | `|R(L₁)| + |R(L₂)| − |R(q_L)| = -1` — BR's `rotation` field at `ε = 0` | **PROVED**, standard axioms only |
| 25602 | **`w6r_exists_rotation hn g h h₁ h₂`** | `∃ δ > 0, ∀ t < δ, ∀ T₀ ∈ w4_EligDec hn g h t, ∀ {r η δ'} hloc ht, IsDecomposition hn hP₀ T₀ → IsDecomposition … (s7b_pre (w5b_ι₁ …) (lift T₀)) → IsDecomposition … (s7b_pre (w5b_ι₂ …) (lift T₀)) → wt(q_L) ≠ 0 → (s7f_Interlacing → ⟨ε = 1 identity⟩) ∧ (¬ s7f_Interlacing → ⟨ε = 0 identity⟩)` | PROVED modulo `w5r_box_corners` and `w6r_box_centreCorners` (radii intersected) |
| 25337 | `w6r_CentreCornerData hn g h h₁ h₂ t T₀ : Prop` | `∃ j j₁ j₂ (e : {i // i ≠ j₁} ⊕ {i // i ≠ j₂} ≃ {i // i ≠ j}), ∀ x, principalTurn (w6r_Lstar …) (e x).1 = Sum.elim (fun y => principalTurn (ccp L₁) y.1) (fun y => principalTurn (ccp L₂) y.1) x` | the consumed Prop (definition) |
| 25595 | **`w6r_box_centreCorners hn g h h₁ h₂`** | `∃ δ > 0, ∀ t < δ, ∀ T₀ ∈ w4_EligDec hn g h t, w6r_CentreCornerData hn g h h₁ h₂ t T₀` | **BLACK BOX — the ONLY sorry of this unit** |

**Which form is delivered.** Per-`(t, T₀)`: the two theorems take the corner data and the centre data as HYPOTHESES `hCC hL` (no radius);
the GLUE already has `hCC t ht₄ T₀ hmem` inside `w4_box_returnedRows` (from `w5r_box_corners`) and gets `hL` the same way from
`w6r_box_centreCorners`.  Radius form: `w6r_exists_rotation` (both identities in one conjunction, all of BR's box binders universally
quantified after `T₀ ∈ w4_EligDec`).  BR's boxes themselves are per-`t` WITHOUT a radius, so neither form can replace their bodies
directly: the GLUE threads a radius (as W5 did for `w5_box_branch` ← `w5r_box_branch`), restating `w5b_interlacingData` /
`w5b_noninterlacingData` (3-line wrappers over the boxes) under it.

## 2. The block (25097-25627, `section W6Rot` … `end W6Rot`; variables of `W4Bigon`; `section W6RotAt` adds `t T₀ {r η δ} hloc ht hT`
and, after the turn lemmas, `hT₀ hS₁ hS₂` — included per theorem)

| line | declaration | content |
|---|---|---|
| 25123 | `w6r_sign_eq_of_ne_zero g ht hcont hne b : ∀ u, |u| ≤ t → sign (ψ u) = sign (ψ (sideTime b t))` | A2's `s7a2_pos_of_ne_zero` device read for the SIGN (continuous, nonvanishing on `|u| < δ` ⇒ constant sign on the connected `[−t, t]`) |
| 25146/25153 | `w6r_principalAngle_smul_right/_left (hc : 0 < c)` | `principalAngle u (c • v) = principalAngle u v`, `principalAngle (c • u) v = …` (`principalAngle_smul` with `1 • _`) |
| 25167 | **`w6r_principalTurn_of_splice`** (§4) | the splice lemma on abstract polygons `Q₁ Q₂ Q` |
| 25261 | **`def w6r_Lstar hn g h t T₀`** | `s7a2_cornerFamily hn g (s7f_side g M a) (s7f_lift hn g h t T₀) (w5r_qH …) g.zeroParameter : LabelledTuple (ccpCornerCount … q_H)` — the corner marks of `q_H` read on `g.center` |
| 25269 | `w6r_Lstar_regular hloc ht hT : Regular L*` | `s7a2_cornerFamily_regular_centre` at `hSp := s7fc_hSp'` (every corner mark of `q_H` persistent) |
| 25275 | `w6r_Lstar_rotation hloc ht hT : rotationNumber L* = carrierRotation hn hP₂ (lift T₀) q_H` | `s7a2_rotation_centre` (A2's family is continuous and regular on `|u| ≤ t`; this is `s7i_full_rotation_germ_centre`'s content for it) |
| 25284 | `w6r_family_turn hloc ht hT u (hu : |u| ≤ t) j : turn (family u) j = sign (det (edge (g.curve u) (s7a2_inEdge m_j)) (edge (g.curve u) (s7a2_outEdge m_j)))` | the `hdet` computation of `s7a2_cornerFamily_regular`: `s7a2_cornerFamily_edge` (edges = ψ • original edge directions), `s7a2_psi_pos` (ψ > 0 on `|u| ≤ t`), `s7a2_corner_edges`, `s7a2_det_smul_smul`, `sign_mul` |
| 25306 | **`w6r_turn_Lstar hloc ht hT j : turn L* j = turn (ccp q_H) j`** | `w6r_family_turn` at `u = 0` and `u = sideTime b t` (where the family is `ccp q_H`, `s7a2_cornerFamily_side_self`) + `w6r_sign_eq_of_ne_zero` on `ψ u := det(edge (g.curve u) E_in, edge (g.curve u) E_out)` (continuous: `continuousAt_det`, `continuous_edge`, `g.continuous_curve`; nonvanishing on `|u| < δ`: `s7a2_corner_det_ne_zero`, which covers vertex marks INCLUDING `μ_M` — the germ's chirotopes off the contact triple, `s7a2_turn_ne_zero`) |
| 25337 | `def w6r_CentreCornerData` | §1 |
| 25359 | `w6r_weight_qH hloc ht hT₀ hW : wt(q_H) ≠ 0` | `w5r_carrierWeight_e … hT₀ q_L`, `unfold w5b_qL`, `Equiv.apply_symm_apply` (`w5b_qH ≡ w5r_qH` by `exact`) |
| 25368 | `w6r_rotationInt_qL hloc ht hT : |R(q_L)| = |R(q_H)|` | `unfold w5b_qL; rw [w5s_qL_eq]; (w5s_rotation …).symm` |
| 25376 | `w6r_patterns_interlacing hI hW' hCC : (∀ i, turn (ccp q_H) i = s₀) ∧ (∀ i, turn (ccp L₁) i = s₀) ∧ (∀ i, turn (ccp L₂) i = s₀)` | `s7c_uniform_halves_of_interlacing` on the corner data's `j j₁ j₂ e he hj₁ hj₂ hj` (`hj` reduced by `simp only [hI, ↓reduceIte]`) |
| 25390 | `w6r_patterns_noninterlacing hI hW' hCC : ∃ j₁ j₂, (∀ i, turn (ccp q_H) i = −s₀) ∧ turn (ccp L₁) j₁ = s₀ ∧ (∀ i ≠ j₁, … = −s₀) ∧ turn (ccp L₂) j₂ = s₀ ∧ (∀ i ≠ j₂, … = −s₀)` | `s7c_dissent_halves_of_noninterlacing` |
| 25414 | `w6r_signType_eq_zero_of_neg_eq : -s = s → s = 0` | `cases s <;> simp_all` |
| 25419/25429/25438 | `w6r_Lstar_contact (hj : ccpCornerMark q_H j = inl M) : L* j = g.center M`; `w6r_ccp_L₁_contact (hj₁ : ccpCornerMark L₁ j₁ = inl 0) : ccp L₁ j₁ = g.center M`; `w6r_ccp_L₂_contact` | `s7a2_point_inl` (+ `g.center = g.curve g.zeroParameter`, `rfl`); `ccpCornerPolygon_apply`, `markPosition_evaluation_vertex`, `firstHalf_zero` / `secondHalf_zero` |
| 25452 | **`w6r_centreCornerData_of_splice hS₁ hS₂ hj hj₁ hj₂ e hpt hsucc₁ hsucc₂ hfirst₁ hlast₂ hsplice hcol : w6r_CentreCornerData`** (§4) | the splice lemma at `L*, ccp L₁, ccp L₂` with the three contact lemmas |
| 25495 | **`w6r_rotation_interlacing`** | §3 |
| 25530 | **`w6r_rotation_noninterlacing`** | §3 |
| 25595 | **`w6r_box_centreCorners`** | BLACK BOX (sorry) |
| 25602 | **`w6r_exists_rotation`** | radii of `w5r_box_corners` and `w6r_box_centreCorners` intersected (`min δ₁ δ₂`) |

## 3. The proofs of the two rotation identities

Common: `hT := w5s_hT … hT₀` (the lift is a decomposition); `hW' := w6r_weight_qH … hW` (`wt(q_H) ≠ 0`); `hreg := w6r_Lstar_regular`,
`hreg₁ hreg₂ := ccpCornerPolygon_regular _ h₁ hS₁ L₁ / … h₂ hS₂ L₂`; sizes `≥ 3` by `ccpCornerCount_ge_three` (`hS₁`, `hS₂`, `hT`).

**`ε = 1`.** `⟨hall, hall₁, hall₂⟩ := w6r_patterns_interlacing hI hW' hCC` (all three carriers uniform of sign `s₀`); `⟨j, j₁, j₂, e, he⟩ := hL`;
`hallL : ∀ i, turn L* i = s₀` by `w6r_turn_Lstar`; `s7i_interlacing_absolute hk₁ hk₂ hk hreg₁ hreg₂ hreg e he (w5r_sgn_ne_zero g h t) hall₁ hall₂ hallL :
|rotationNumber L*| = |rotationNumber (ccp L₁)| + |rotationNumber (ccp L₂)|`; `rw [w6r_Lstar_rotation]`; `rw [w6r_rotationInt_qL]`; cast to ℝ with
`carrierRotationInt_cast` (`hT`, `hS₁`, `hS₂`), `exact_mod_cast`.  **Note** that the centre data's `j j₁ j₂ e` are NOT tied to the corner
data's: under `wt(q_H) ≠ 0` all turns of `ccp q_H` are equal, so `hall` holds at every index and any `e` works.

**`ε = 0`.** `⟨j₁', j₂', hall, hj₁', hrest₁', hj₂', hrest₂'⟩ := w6r_patterns_noninterlacing hI hW' hCC` (`ccp q_H` uniform of sign `−s₀`, `L₁`
with the unique dissent `s₀` at `j₁'`, `L₂` at `j₂'`); `⟨j, j₁, j₂, e, he⟩ := hL`; `hallL : ∀ i, turn L* i = −s₀`; the SignType form of `he`
(`hsgn`, via `principalTurn_sign` on the three regular polygons: `turn L* (e x).1 = Sum.elim (turn (ccp L₁) ·) (turn (ccp L₂) ·) x`); **the
excluded corners are the dissents**: if `j₁' ≠ j₁` then `hsgn (inl ⟨j₁', _⟩)` reads `−s₀ = turn L* _ = turn (ccp L₁) j₁' = s₀`, so `s₀ = 0`
(`w6r_signType_eq_zero_of_neg_eq`), contradicting `w5r_sgn_ne_zero`; likewise `j₂' = j₂`; `subst`; `s7i_noninterlacing_absolute hk₁ hk₂ hk hreg₁
hreg₂ hreg e he hs₀ hj₁' hrest₁' hj₂' hrest₂' hallL : |rot (ccp L₁)| + |rot (ccp L₂)| − |rot L*| = −1`; the same rewrites and cast.

Both compiled on the FIRST probe against the prefix olean (no failed attempt; the reassessment rule was not triggered).

## 4. The black box `w6r_box_centreCorners`, why it is needed, and the bridge to close it

**Why `w5r_CornerData` does not suffice (rule 3 disclosure).** The task's route reads "U110-I … with the correspondence `e, he` from
`w5r_box_corners` in principalTurn form (exact on the centre)".  `w5r_CornerData` (24544) states `he` as `turn (ccp q_H) (e x).1 =
Sum.elim (turn (ccp L₁) ·) (turn (ccp L₂) ·) x` — SignType turns on `P₂(t)`.  U110-I's `s7i_interlacing_absolute` /
`s7i_noninterlacing_absolute` (and the ledgers `s7i_rotation_ledger_*` beneath them) need `principalTurn Q (e x).1 = Sum.elim
(principalTurn Q₁ ·) (principalTurn Q₂ ·) x` — angles — because `2π · rot` is the SUM of principal turns; no sign information can
recover it (a uniform polygon of sign `s₀` with `k` corners has any rotation number `≥ 1` compatible with `k`).  So the angle form is
new content, not a reading of the declared box, and rule 2 forbids restating `w5r_box_corners`.  It is stated here as
`w6r_CentreCornerData` on `L*` (where the angle identity is EXACT, the halves' corner polygons and `L*` living on the same points of
`g.center`), consumed through the radius-form `w6r_box_centreCorners`.  Nothing else of the corner data is assumed on the centre:
the sign data of the three contact corners and of all other corners is transported from `P₂(t)` by `w6r_turn_Lstar` (§2), and at
`ε = 0` the excluded corners are identified with the dissents (§3) — hence the box carries ONLY the principal-turn clause, with
`j j₁ j₂ e` free.

**Truth of the box (checked on paper, not in Lean).** `L*`'s vertices are `s7a2_point g.center (ccpCornerMark q_H j)`: a vertex mark
`inl i ↦ g.center i`, a selected visit `↦` the centre crossing point of its two edges (persistent, `s7fc_hSp'`).  `ccp L₁`'s vertices are
`s7a2_point (firstHalf g.center M a) m` (`s7a2_point_eq_evaluation`): the half's vertices are centre vertices (vertex `0 = g.center M`,
`firstHalf_zero`) and its visits centre crossing points.  Off the contact, corresponding corners are the same points, and the merged
cyclic order of `q_H`'s corner list is `μ_M`, then `L₁`'s corners after its vertex `0` (leaving `μ_M` along `E_M`, returning along `E_a`),
then `L₂`'s corners after its vertex `0` (continuing along `E_a`, returning along `E_{M−1}` to `μ_M`) — so equal edges everywhere except
at the two corners adjacent to the contact ON `E_a` (the last corner `c` of `L₁`, the first corner `c'` of `L₂`), where `L*`'s spliced
edge `c → c'` and the halves' edges `c → g.center M`, `g.center M → c'` are positive multiples of `E_a` (`c`, `g.center M = edgePoint a r`,
`c'` in this order on `E_a`), and `principalAngle` ignores positive rescaling (`principalAngle_smul`).  (Whether `L₁` or `L₂` comes
first after `μ_M` depends on which half `firstHalf` is; the splice lemma is stated for "`Q₁` first" and applies with the roles of
`Q₁, Q₂` swapped through `Equiv.sumComm`.)

**The bridge, PROVED (25167 `w6r_principalTurn_of_splice`; 25452 `w6r_centreCornerData_of_splice`).** For abstract regular-or-not
polygons `Q₁ : LabelledTuple k₁`, `Q₂ : LabelledTuple k₂`, `Q : LabelledTuple k` (`3 ≤ k₁, k₂`), contact indices `j₁ j₂ j` and
`e : {i ≠ j₁} ⊕ {i ≠ j₂} ≃ {i ≠ j}`, from
- `hpt : ∀ x, Q (e x).1 = Sum.elim (Q₁ ·.1) (Q₂ ·.1) x` (corresponding corners are the same POINTS),
- `hc₁ : Q j = Q₁ j₁`, `hc₂ : Q j = Q₂ j₂` (one contact point),
- `hsucc₁ : ∀ y y', y'.1 = y.1 + 1 → (e (inl y')).1 = (e (inl y)).1 + 1`, `hsucc₂` likewise (order-preserving on each half),
- `hfirst₁ : ∀ y, y.1 = j₁ + 1 → (e (inl y)).1 = j + 1` (`Q₁`'s first corner after the contact follows `j`),
- `hlast₂ : ∀ y, y.1 + 1 = j₂ → (e (inr y)).1 + 1 = j` (`Q₂`'s last corner before the contact precedes `j`),
- `hsplice : ∀ y y', y.1 + 1 = j₁ → y'.1 = j₂ + 1 → (e (inl y)).1 + 1 = (e (inr y')).1` (the splice),
- `hcol : ∃ v α β, 0 < α ∧ 0 < β ∧ Q j − Q₁ (j₁ − 1) = α • v ∧ Q₂ (j₂ + 1) − Q j = β • v` (the contact point strictly between the two
  splice corners on a line),
it concludes `∀ x, principalTurn Q (e x).1 = Sum.elim (principalTurn Q₁ ·.1) (principalTurn Q₂ ·.1) x`.  Proof: for `inl y` the incoming
edge is inherited (`hsucc₁` at `y − 1`, or `hfirst₁` + `hc₁` when `y − 1 = j₁`); the outgoing edge is inherited (`hsucc₁`) unless
`y + 1 = j₁`, where it is `(β + α) • v` against `Q₁`'s `α • v` and `w6r_principalAngle_smul_right` finishes; symmetric for `inr y` with
`hlast₂`/`hc₂` and `hsplice` + `w6r_principalAngle_smul_left`.  `w6r_centreCornerData_of_splice` instantiates it at `L*, ccp L₁, ccp L₂`
with the contact corners given as MARKS (`ccpCornerMark q_H j = inl M`, `ccpCornerMark L₁ j₁ = inl 0`, `ccpCornerMark L₂ j₂ = inl 0`),
discharging `hc₁ hc₂` by `w6r_Lstar_contact`, `w6r_ccp_L₁_contact`, `w6r_ccp_L₂_contact` and taking `hcol` with `g.center M` in
place of `Q j`; so the box reduces to: **the corner list of `q_H` is the merge of the two halves' corner lists at `μ_M` (W6-COR's
construction, at the MARK level: `hpt` = the centre points of corresponding marks agree, `hsucc/hfirst/hlast/hsplice` = the merged
cyclic order) plus the collinearity `hcol` on `E_a`** (the two splice corners lie on `E_a` on either side of parameter `r`:
`s7a2_edgeParameter_interior`, the parameter order of `c`, `μ_M`, `c'` on `E_a`).  None of these mark-level facts can be read from
`w5r_CornerData`, whose `e` is existential.

## 5. Honest state

- **Sorry-free:** `w6r_rotation_interlacing`, `w6r_rotation_noninterlacing` (the two deliverables, given `hCC hL`), `w6r_turn_Lstar`,
  `w6r_family_turn`, `w6r_Lstar_regular`, `w6r_Lstar_rotation`, `w6r_weight_qH`, `w6r_rotationInt_qL`, `w6r_patterns_*`,
  `w6r_principalTurn_of_splice`, `w6r_centreCornerData_of_splice`, the contact lemmas — all `[propext, Classical.choice, Quot.sound]`.
- **Sorried, LIVE for this unit's radius form:** `w6r_box_centreCorners` (25595) — the ONE open Prop: `∃ δ > 0, ∀ t < δ, ∀ T₀ ∈ w4_EligDec
  hn g h t, w6r_CentreCornerData hn g h h₁ h₂ t T₀` (statement §1).  `w6r_exists_rotation` carries `sorryAx` through it and through
  `w5r_box_corners` (W6-COR's box, called, not restated).
- **Consumed from other units (black boxes, rule 2):** `w5r_box_corners` (ROW's Prop `w5r_CornerData`, to be closed by W6-COR) — by CALL
  in `w6r_exists_rotation`; as hypothesis `hCC` in the per-`(t, T₀)` theorems.  `w6r_box_centreCorners` — stated here (§4), to be closed
  by W6-COR / GLUE through `w6r_centreCornerData_of_splice`.
- **No frozen statement, name or docstring touched; no body replaced** (`25096a25097,25627` only).  `thm_C_S7`'s axioms are unchanged
  (`sorryAx` through the bigon leaf's own sorry; `w4_box_returnedRows` through the four W5 live boxes, none of which this unit fills).
- **Not done / not attempted:** proving `w6r_box_centreCorners` itself — it is W6-COR's corner-list merge read on the centre (RT's mark
  transport `w5t_ct_*`, `w5t_markTurn_*`, the half tuples' vertex/visit points), 700-1,100 lines by the W5 estimate, and a duplicate of
  the COR lane; under rule 2 this unit may not build on COR's `e` except through `w5r_box_corners`.

## 6. Method audit (reassessment rule)

No lemma took two failed attempts.  Probe record (`<scratchpad>/w6rot/`, prefix olean `pfx/W6Prefix.olean` = `W5[1..25096]` + closing
`end`s, 47 s; ~30 s per probe): Probe1 (L* definitions + `w6r_turn_Lstar`): 2 errors, both the argument order of A2's
`s7a2_cornerFamily_regular_centre` / `s7a2_rotation_centre` (`… b S hSp hS q`, the `include` order, unlike `s7a2_psi_pos`'s `… b S hS hSp q`);
Probe2 (the whole rotation block): 0 errors (deprecated `if_pos`/`if_neg` → `simp only [hI, ↓reduceIte]`; three unused-binder warnings in the
radius statement → `_hT₀ _hS₁ _hS₂`); Probe3 (splice lemma): 1 error class — `rw [hpt (inl ⟨…⟩)]` leaves `Sum.elim … (inl …)` unreduced →
local `hpt₁ hpt₂ : ∀ y, Q (e (inl y)).1 = Q₁ y.1` by `fun y => hpt (inl y)`; Probe4/5 (full block, then + contact lemmas): 0 errors.  One design
decision, taken at the start after reading U110-I's statements: the black box carries the principal-turn clause ONLY (no sign data, no
pinning of `j j₁ j₂`), because `w6r_turn_Lstar` + the weight hypothesis supply every sign on `L*` and force the dissents at `ε = 0`.

## 7. Verification record

```
cd work/lean && lake env lean ../drafts/corner/W6_ROT.lean          # 0 errors; 11 × "declaration uses sorry" (4439 18055 18496 23881 24278 24287 24304 25071 25090 25595 25716); 55 s
cd work/lean && lake env lean <scratchpad>/w6rot/W6_ROT_axioms.lean  # the file + 20 #print axioms lines after `end SM` (log axioms.log): §5
grep -c sorry work/drafts/corner/W5_Assembled.lean work/drafts/corner/W6_ROT.lean     # 22 → 23
diff work/drafts/corner/W5_Assembled.lean work/drafts/corner/W6_ROT.lean | grep "^[0-9]"   # 25096a25097,25627
python3 work/drafts/corner/tools/stmt_check.py work/drafts/corner/W6_ROT.lean --base work/drafts/corner/W3_Skeleton.lean   # 5/5 PASS
python3 work/drafts/corner/tools/clash_scan.py work/drafts/corner/W6_ROT.lean   # duplicates [] / full_name_clashes {} / 1385 new decls
tail -n 43 work/drafts/corner/W6_ROT.lean | diff - <(tail -n 43 work/drafts/corner/W3_Skeleton.lean)   # identical
grep -n "#print" work/drafts/corner/W6_ROT.lean   # none
```
Reproduce: `<scratchpad>/w6rot/assemble.py` (assert-guarded; `block.lean` = `pieces/00_sign 00b_splice 00c_lstar 01_turn 02_main 02b_contact
03_thms 04_radius`), probes `Probe1-5.lean` via `lean.sh` against `pfx/W6Prefix.olean` (`build_pfx.sh`).
