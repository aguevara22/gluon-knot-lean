# W5_ROW_REPORT — corner wave 5, unit ROW (prefix `w5r_`; W4_ASSEMBLY_REPORT §5 W5-ROW: the returned row and the radius of Prop B2'), 2026-09-19 ~09:05 UTC / 5:05am ET (under D-AUTH-20260919, no bound)

File: **`work/drafts/corner/W5_ROW.lean`** (20,471 lines, sha256 `d95eab681d6f2507b7051ebf5f210eb93359400730f4fccb6b4582024e8daf22`)
= `W4_Assembled.lean` (19,974 lines, `9c0ec3b7…`) + ONE inserted `w5r_` block + the `sorry` body of `w4_box_returnedRows` replaced.
`diff W4_Assembled.lean W5_ROW.lean` has exactly TWO hunks: `19853a19854,20330` (the block, 477 lines, inserted immediately BEFORE
the docstring of `w4_box_returnedRows`, inside `section W4Bigon` after `end W4BigonAt`) and `19858c20335,20355` (`  sorry` →
the 21-line composition); the deleted side is the single line `  sorry`.  Every existing statement, name and docstring is
byte-identical; `python3 tools/stmt_check.py W5_ROW.lean --base W3_Skeleton.lean` → **5/5 PASS**; `tail -n 43` identical to
`W3_Skeleton.lean`; `tools/clash_scan.py`: `duplicates_in_assembled: []`, `full_name_clashes: {}` (1,057 new declarations, 29 of them
`w5r_`).  No import added, nothing written under `work/lean`.
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W5_ROW.lean`): see §6 — 0 errors, no warning other than the
`declaration uses sorry` notes of the 8 sorried bodies.  **`grep -c sorry`: 16 → 19** (5 → 8 sorried bodies: `w4_box_returnedRows`'s
body removed, the four `w5r_box_*` added; the 11 prose mentions unchanged).

## 0. In one paragraph

**Prop B2' `w4_BigonReturnedRows` is CLOSED MODULO FOUR EXPLICIT BLACK BOXES**, the deliverables of the sibling wave-5 units stated at
DEFINED carriers.  The four contact carriers of an eligible decomposition `T₀` of `P₀(t)` (lift `T`, half preimages `T₁, T₂`) are
definable, no existence box needed: `w5r_qH := owner (Sum.inl M)` on `P₂` (the carrier through the contact vertex `μ_M`),
`w5r_qL := owner (Sum.inl M)` on `P₀` (U110-A's transport carries it to `q_H`: `w5r_e_qL`, from `s7a_sideComponentEquiv_owner` at the
persistent vertex mark), `w5r_L₁ := owner (Sum.inl 0)` of `T₁` on `λ₁` and `w5r_L₂ := owner (Sum.inl 0)` of `T₂` on `λ₂` (vertex `0` of
each half IS the contact vertex `P M`: `firstHalf_zero`, `secondHalf_zero`), and the contact crossing `w5r_x` of the positive lift
`D_H` is `carrierCrossingEquiv.symm ⟨s7f_x, hx⟩` (= SITE's `s7s_liftGen`, `s7s_liftGen_eq_carrierCrossingEquiv`).  The row
`w5r_returnedRow_of` (PROVED, axioms standard + `lit_homfly, lp_lm, lp_lm_uniqueness`, no `sorryAx`) is:
`term₂(T) − term₀(T₀) = wt(q_H)·(c(q_H) − c(q_L))·Π_sp` by FB3's transport (`s7fc_e`, equal weights per carrier
`w5r_carrierWeight_e`, equal coefficients off `q_H` `w5r_coef_spectator`) and the factorisation `w5r_prod_sub_prod`; at `ε = 1`
BLOCK's `s7k_interlacing_row` (SITE's contact data + BR's branch data; the floor `hF` enters there at the two uniform half
contact carriers of the wall's halves), C's `s7c_carrierWeight_interlacing` on the corner data (`wt(q_H) = −s₀ wt(L₁) wt(L₂)`) and
RT's spectator bijection (`Π_sp = Π₁ Π₂`, `w5r_spectator_prod`) give `s₀ · term(T₁) term(T₂)`; at `ε = 0` BLOCK's
`s7k_noninterlacing_row` (either half orientation) or J's `s7j_different_block_entry_at_halves` gives `c(q_H) = c(q_L)`, so the row is
`0`.  The radius (`w4_box_returnedRows`'s new body) intersects F's split radius (`s7f_exists_bigonSplit`), A2's interval-local radius
(`s7a2_exists_intervalLocal`) and the four boxes' radii.  **`thm_C_S7` still carries `sorryAx`**: the bigon leaf keeps the skeleton's
`sorry` (merge rule — its input `w4_box_returnedRows` is not yet sorry-free); its one-line closure is unchanged
(`w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)`), and `w4_box_returnedRows` now carries `sorryAx`
exactly through `w5r_box_transport`, `w5r_box_corners`, `w5r_box_contact`, `w5r_box_branch`.

## 1. Layout of the block (`section W5Row`, lines 19854-20329; `variable (hn) (g) {M a} (h) (h₁) (h₂)` of `section W4Bigon` in scope)

| lines | section | declarations |
|---|---|---|
| 19854-19878 | header docstring | — |
| 19880-19894 | `W5Row` | `w5r_sgn` (def: `s₀` as a `SignType`, `if s7f_side then contactSign else −contactSign`), `w5r_sgn_cast` (`(w5r_sgn : ℤ) = s7f_dirSign * contactSign`), `w5r_sgn_ne_zero` (from `vertex_contact_signs`) |
| 19896-19940 | `W5RowAt` (`variable (t) (T₀)`) | `w5r_ι₁`, `w5r_ι₂` (abbrev: U110-B's half crossing maps), `w5r_T₁`, `w5r_T₂` (abbrev: `s7b_pre ιᵢ (lift T₀)`), **`w5r_qH`**, **`w5r_qL`**, **`w5r_L₁`**, **`w5r_L₂`**, **`w5r_x`** |
| 19942-19999 | `W5RowTransport` (`hloc ht`) | `w5r_e_qL` (`s7fc_e q_L = q_H`), `w5r_carrierWeight_e` (per-carrier weight transport, the summand of FB3's `s7fc_wind_eq`), `w5r_coef_spectator` (FB3's `s7fc_coef_eq` at a carrier `≠ q_H`, via `carrierCrossings_disjoint`) |
| 20001-20141 | `W5RowProps` (`variable (hT)`) | the four consumed Props: **`w5r_TransportData`**, **`w5r_CornerData`**, **`w5r_ContactData`**, **`w5r_DifferentBlockData`** (Prop-structure), **`w5r_BranchData`** (§3) |
| 20143-20182 | `W5RowAlgebra` | `w5r_prod_sub_prod`, `w5r_prod_erase_eq_subtype`, `w5r_spectator_prod`, `w5r_prod_eq_mul_erase` (pure ℤ products) |
| 20184-20295 | `W5RowAt` (`hloc ht`) | **`w5r_returnedRow_of`** — the row at one eligible decomposition (§2) |
| 20297-20329 | `W5Row` | the four black boxes **`w5r_box_transport`**, **`w5r_box_corners`**, **`w5r_box_contact`**, **`w5r_box_branch`** (sorried) |
| 20332-20355 | (W4 glue) | `w4_box_returnedRows` with the new 21-line body (§4) |

Signatures (from `#check`): `w5r_qH hn g h t T₀`, `w5r_qL hn g t T₀`, `w5r_L₁ hn g h h₁ t T₀`, `w5r_L₂ hn g h h₂ t T₀`,
`w5r_x hn g h t T₀ hT hx`, `w5r_TransportData hn g h h₁ h₂ t T₀ hT`, `w5r_CornerData hn g h h₁ h₂ t T₀`, `w5r_ContactData hn g h t T₀ hT`,
`w5r_DifferentBlockData hn g h h₁ h₂ t T₀ hT hT₀ hT₁ hT₂`, `w5r_BranchData hn g h h₁ h₂ t T₀ hT`,
`w5r_returnedRow_of hn g h h₁ h₂ t T₀ hloc ht hF hsplit hmem hRT hCC hSITE hBR`.

## 2. PROVED (25 declarations; axioms §6)

* `w5r_returnedRow_of hF hsplit hmem hRT hCC hSITE hBR : term₂(lift T₀) − term₀(T₀) = ε · (δ_dir · s) · (term(T₁) · term(T₂))` — exactly the
  body of `w4_ReturnedRow` at `T₀` (the `w5r_Tᵢ` abbreviations unfold to the frozen `s7b_pre (s7b_*CrossingQ …) (s7f_lift …)`).
  Proof (85 lines): `hT` from membership, `hT₀` by `s7fc_isDecomposition_lift`, `hT₁ hT₂` as the components of `w4_eligibleEquiv
  hsplit ⟨T₀, hmem⟩` (their `.1.1/.2.1` are `s7b_pre ιᵢ (lift T₀)` by `rfl`); the four terms by `s7e_term_of_decomposition`, `unfold
  wind cornerProduct`, `← Finset.prod_mul_distrib` ×4; the low product re-indexed by `Fintype.prod_equiv (s7fc_e …)` with
  `w5r_carrierWeight_e`; `w5r_prod_sub_prod` at `q_H` with `w5r_coef_spectator`; `e.symm q_H = q_L` (`w5r_e_qL`); `← mul_sub`;
  `by_cases hε`.  `ε = 1`: `s7k_interlacing_row … hc v hv DA i j hb` (`hrow`), `s7c_carrierWeight_interlacing … jc j₁ j₂ (w5r_sgn_ne_zero)
  hj hj₁ hj₂ ec hec` (`hwtH`), `w5r_spectator_prod … e` on `hwt`/`hcf` (`hsp`), then `rw [hsp, hrow, hwtH, ite_eq_left hε, ← w5r_sgn_cast,
  w5r_prod_eq_mul_erase _ L₁, w5r_prod_eq_mul_erase _ L₂]; ring`.  `ε = 0`: `c(q_H) − c(q_L) = 0` from `s7k_noninterlacing_row` (both
  orientations) or `s7j_different_block_entry_at_halves` (both coefficients `0`), then `rw [h0, ite_eq_right hε]; ring`.
* `w5r_e_qL`, `w5r_carrierWeight_e`, `w5r_coef_spectator` (U110-A/FB3 transport read at the defined carriers; standard axioms /
  `+ lit_homfly, lp_lm, lp_lm_uniqueness` for the coefficient).
* `w5r_sgn_cast`, `w5r_sgn_ne_zero`; the four algebra lemmas; the eleven defs/abbrevs/Prop-defs of §1.
* **`w4_box_returnedRows hF : w4_BigonReturnedRows hn g h h₁ h₂`** — body replaced (§4); carries `sorryAx` through the four boxes only.

Inputs used (all proved in W4 or the library): `w4_mem_EligDec`, `w4_eligibleEquiv`, `s7f_exists_bigonSplit`, `s7a2_exists_intervalLocal`,
`s7fc_e`, `s7fc_isDecomposition_lift`, `s7fc_coef_eq`, `s7fc_hs/hpar/hL/hSS'/hSp/hSp'`, `s7a_sideComponentEquiv_owner`,
`s7a_ccpCornerCount_eq`, `s7a_turn_ccpCornerPolygon`, `s7a_side_turn/sgn`, `s7c_carrierWeight_eq_sel`, `s7c_map_univ_eq_of_equiv`,
`s7c_carrierWeight_interlacing`, `s7c_neg_sign_ne_zero`, `carrierCrossings_disjoint`, `carrierCrossingEquiv`, `s7e_term_of_decomposition`,
`s7k_interlacing_row`, `s7k_noninterlacing_row`, `s7j_different_block_entry_at_halves`, `vertex_contact_signs`, `firstHalf_zero`/
`secondHalf_zero` (documentation only), Mathlib `Finset.mul_prod_erase`, `Finset.prod_subtype`, `Fintype.prod_equiv`, `Fintype.prod_sum_type`.

## 3. BLACK BOXES — exactly what this unit consumes (rule (2)), at the DEFINED carriers

All four are `∃ δ > 0, ∀ t : g.SideParameter, t.val < δ → ∀ T₀ ∈ w4_EligDec hn g h t, [∀ hT : IsDecomposition hn hP₂ (lift T₀),] <Prop>`
with `hP₂ := s7f_hP₂ g M a t`, `hP₀ := s7f_hP₀ g M a t`, `T := s7f_lift hn g h t T₀`, `T₁ := w5r_T₁ = s7b_pre ι₁ T`, `T₂ := w5r_T₂ = s7b_pre ι₂ T`,
`q_H := w5r_qH = owner hn hP₂ T (Sum.inl M)`, `q_L := w5r_qL = owner hn hP₀ T₀ (Sum.inl M)`, `L₁ := w5r_L₁ = owner … h₁ T₁ (Sum.inl 0)`,
`L₂ := w5r_L₂ = owner … h₂ T₂ (Sum.inl 0)`, `x := w5r_x hT hx = (carrierCrossingEquiv hn hP₂ T q_H hT).symm ⟨s7f_x hn h t, hx⟩`,
`s₀ := w5r_sgn g M a` (`(s₀ : ℤ) = s7f_dirSign * contactSign = χ(P₀)`, `s7f_s₀_eq_chi`), `hnᵢ := (contactHalfSizes_bounds hn h.1.1).i.1`.
Decomposition proofs `hT₀ hT₁ hT₂` are universally quantified INSIDE the Props (proof-irrelevant; the consumer supplies
`s7fc_isDecomposition_lift` and `w4_eligibleEquiv`'s components), so no Prop mentions `hloc`/`hsplit`.

1. **`w5r_box_transport` — unit W5-RT** (`w5r_TransportData hn g h h₁ h₂ t T₀ hT`, W4 §5 W5-RT; sm-4:556-575):
   `s7f_x hn h t ∈ carrierCrossings hn hP₂ T q_H ∧ s7f_y hn h t ∈ carrierCrossings hn hP₂ T q_H ∧`
   `∃ e : {q : Component hn hP₂ T // q ≠ q_H} ≃ {L : Component hn₁ h₁ T₁ // L ≠ L₁} ⊕ {L : Component hn₂ h₂ T₂ // L ≠ L₂},`
   `(∀ q, carrierWeight hn hP₂ T q.1 = Sum.elim (fun L => carrierWeight hn₁ h₁ T₁ L.1) (fun L => carrierWeight hn₂ h₂ T₂ L.1) (e q)) ∧`
   `∀ hT₁ hT₂ q, cornerCoefficient hn hP₂ T q.1 hT = Sum.elim (fun L => cornerCoefficient hn₁ h₁ T₁ L.1 hT₁) (fun L => cornerCoefficient hn₂ h₂ T₂ L.1 hT₂) (e q)`.
   Content: the first-return law of the returned (newborn-free) configuration — the traversal `x_ℓ → μ_M → y_ℓ → [A] → (y_a, x_a in
   either order) → [B] → x_ℓ` is one carrier (FB2's `s7fb_mark`/`s7fb_BigonTransport` engine with the unit component removed and the
   two `μ_M` copies merged), and every other carrier of `T` is the image of one half carrier with equal turns (weights), rotations
   (FB2 Part E family) and records (coefficients through `CB.positiveLiftRecordIso` / U110-D).  W4 §5 estimate 1,000-1,500 lines.
2. **`w5r_box_corners` — unit W5-RT (or W5-BR)** (`w5r_CornerData hn g h h₁ h₂ t T₀`; sm-4:576-600, eq. s7c:angle-orders):
   `∃ (j : ZMod (ccpCornerCount hn hP₂ T q_H)) (j₁ : ZMod (ccpCornerCount hn₁ h₁ T₁ L₁)) (j₂ : ZMod (ccpCornerCount hn₂ h₂ T₂ L₂))`
   `(e : {i // i ≠ j₁} ⊕ {i // i ≠ j₂} ≃ {i // i ≠ j}),`
   `(∀ x, turn (ccpCornerPolygon hn hP₂ T q_H) (e x).1 = Sum.elim (fun y => turn (ccp L₁) y.1) (fun y => turn (ccp L₂) y.1) x) ∧`
   `turn (ccp L₁) j₁ = s₀ ∧ turn (ccp L₂) j₂ = s₀ ∧ turn (ccp q_H) j = (if s7f_Interlacing hn h t then s₀ else -s₀)`.
   This is the `e`/`he` of C's `s7c_carrierWeight_interlacing` (with `turn`); BR's `s7k_interlacingData_of_patterns` wants the same
   correspondence with `principalTurn` (`he`) — one unit should build it and both read it.  Truth check (§5): with `E_a` horizontal
   and both neighbour vectors of `M` above it, `P₀` has `M` above the line (`s₀ = +1`), λ₁'s contact corner turns from `E_a` to `E_M`
   (angle `β`, sign `+`), λ₂'s from `E_{M−1}` to `E_a` (angle `π − α`, sign `+`), and `q_H`'s from `E_{M−1}` to `E_M` has sign
   `sgn sin(β − α + π) = +` iff `β < α` iff `x_a < y_a` iff interlacing — exactly the stated Prop.
3. **`w5r_box_contact` — unit W5-SITE** (`w5r_ContactData hn g h t T₀ hT`; W4 §5 W5-SITE):
   `∀ (hT₀ : IsDecomposition hn hP₀ T₀) (hx : s7f_x ∈ carrierCrossings hn hP₂ T q_H) (_hy : s7f_y ∈ carrierCrossings hn hP₂ T q_H),`
   `s7k_ContactRowData hn hP₂ hP₀ hT hT₀ q_H q_L (w5r_x hT hx)` — i.e. `site : ∃ B : BigonData ((positiveLift q_H).switch x), Nonempty
   (RecordIso B.reducedRecord (positiveLift hn hP₀ T₀ q_L hT₀).record)` and `rotation : |carrierRotationInt q_H| = |carrierRotationInt q_L|`.
   Recipe: W4_SITEH_REPORT §4 with `S := T`, `S' := T₀`, `hSS' := s7fc_hSS'`, `hSp := s7fc_hSp'`, `hSp' := s7fc_hSp`, `q := q_H`,
   `hxq hyq` through `s7s_mem_geoCarrierCrossings_iff`, `xPair hx = s7f_x` by `Subtype.ext (Finset.pair_comm _ _)`; `s7s_site` gives
   the `BigonData` at `s7s_liftGen … = w5r_x` (`s7s_liftGen_eq_carrierCrossingEquiv`) and `s7s_rii_witnesses`/`BigonData.reducedRecord`
   with `hrec := s7sh_hrec_prop_side` give the record clause at `D_L = positiveLift … (s7a_sideComponentEquiv … q_H) …`, which is
   `positiveLift … q_L` by `w5r_e_qL` (`s7fc_e` IS `s7a_sideComponentEquiv`); the rotation through the wall is the family of the contact
   carrier (W2_S7A2 §4(ii) / FB2 Part E adapted).  Estimate 600-1,000 lines.
4. **`w5r_box_branch` — unit W5-BR** (`w5r_BranchData hn g h h₁ h₂ t T₀ hT`; W4 §5 W5-BR): `∀ hT₀ hT₁ hT₂ hx _hy,`
   `(s7f_Interlacing hn h t → ∃ (v : (positiveLift hn hP₂ T q_H hT).Γ.Visit) (DA : Diagram) (i j : Fin DA.Γ.c), v.1 = w5r_x hT hx ∧`
   `  s7k_InterlacingData hn hP₂ hP₀ hT hT₀ q_H q_L hn₁ hn₂ h₁ h₂ hT₁ hT₂ L₁ L₂ v DA i j) ∧`
   `(¬ s7f_Interlacing hn h t → (∃ v DA i j, v.1 = w5r_x hT hx ∧ (s7k_NoninterlacingData … hn₁ hn₂ h₁ h₂ hT₁ hT₂ L₁ L₂ v DA i j ∨`
   `  s7k_NoninterlacingData … hn₂ hn₁ h₂ h₁ hT₂ hT₁ L₂ L₁ v DA i j)) ∨ w5r_DifferentBlockData hn g h h₁ h₂ t T₀ hT hT₀ hT₁ hT₂)`.
   `w5r_DifferentBlockData` (Prop-structure, fields `fH fL mH mL rotation rotationH pattern₁ pattern₂`) = the hypotheses of
   `s7j_different_block_entry_at_halves` / `s7k_different_block_row` at `q_H q_L L₁ L₂`.  The ε = 0 disjunction is a DELIBERATE
   widening of W4 §5's single shape: the printed proof has two alternatives (same-block sm-4:736-769, where the curl `y` sits on
   component 1 ↔ `L₁` — the A-boundary component, sm-4:585-587, so the first `s7k_NoninterlacingData` orientation is the expected
   one; different-block sm-4:785-813), and the swapped orientation is offered only as insurance.  BR delivers ONE disjunct.
   `DA` may be SITE's `D₀` of `s7s_cornerHomfly_skein` (its record clause is the `record` field).  Estimate 800-1,300 lines.

What is NOT consumed: no floor-side Prop (the floor enters only inside `s7k_interlacing_row` / `s7k_noninterlacing_row` /
`s7j_different_block_entry_at_halves`, at the wall's halves `h₁ h₂` — the literal domain of `s7j_half₁_floor`/`s7j_half₂_floor`),
no `hsing` (B3's), no K-side Prop.  `s7j_interlacing_entry_at_halves` / `s7j_noninterlacing_entry_at_halves` (W4 §5's named entries)
are not needed: BLOCK's `s7k_*_row` theorems take the branch data with the pattern fields and read the floor themselves with the
same `hF.slot_le_of_signed` at the same carriers; J's `_at_halves` forms remain available to a BR that prefers to deliver the
extracted Laurent row instead.

## 4. The body of `w4_box_returnedRows` (lines 20335-20355) and the radius

`s7f_exists_bigonSplit` (δ₁, `hsplit`), `s7a2_exists_intervalLocal hn g M a h.1` (δ₂, `hloc`), the four boxes (δ₃…δ₆);
`δ := min (min δ₁ δ₂) (min (min δ₃ δ₄) (min δ₅ δ₆))`; at `t < δ`, `intro T₀ hmem` (through the `def w4_ReturnedRow`) and
`exact w5r_returnedRow_of hn g h h₁ h₂ t T₀ hloc ht₂ hF (hsplit t ht₁) hmem (hRT t ht₃ T₀ hmem _) (hCC t ht₄ T₀ hmem)
(hSITE t ht₅ T₀ hmem _) (hBR t ht₆ T₀ hmem _)`.  The bigon leaf `s7_bigon_law_at` (20419) keeps the skeleton's `sorry` (merge rule:
its input is not sorry-free); nothing else changed.  The leaf's closure line stays
`w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)` (`w4_s7_bigon_law_at_of` is sorry-free, §6).

## 5. Method audit, deviations, truth of the consumed shapes

* Reassessment rule: **not triggered**.  Two harness compiles (`Test1`: 3 mechanical errors — `include h in` missing on
  `w5r_sgn_ne_zero`, `g` dropped in `w5r_ι₁ hn g h t`, `neg_ne_zero` is not a `SignType` lemma (use `s7c_neg_sign_ne_zero`); `Test2`:
  0 errors first time, 3 deprecation notes `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`), then the assembly compiled first time.
  The four pure algebra lemmas compiled first time against Mathlib alone (`<scratchpad>/w5r/Alg.lean`).
* Design deviation from W4 §5 (disclosed): the carriers are DEFINED (`owner` of the contact vertex marks) rather than existentially
  supplied by RT, so the three consumer boxes can be stated and delivered independently of RT; `w5r_qL` is `owner (inl M)` on `P₀`
  rather than `s7fc_e.symm q_H` (they agree, `w5r_e_qL`), keeping `hloc` out of the Props.  The corner correspondence is a box of its
  own (`w5r_box_corners`) because it is the input of C's selector law in the ROW as well as of BR's rotation identities.  The ε = 0
  disjunction of §3.4.  `w5r_ContactData`/`w5r_BranchData` carry an unused `_hy` hypothesis so SITE/BR receive both self-crossing facts.
* Truth: nothing believed false.  §3.2's sign check verifies the corner Prop against the printed turn bookkeeping (sm-4:576-600);
  §3.1's first clause is the printed sentence sm-4:556-560 (one full contact carrier); §3.3 is SITE/SITEH's proved chain at the
  defined carriers; §3.4 is BLOCK's interface with BR's two printed alternatives.  No frozen statement needed a change.
* Nothing written under `work/lean`; no import, no `open`, no `notation`, no `set_option` added; every new name is `w5r_`-prefixed;
  the block is inside `section W4Bigon` (its `variable (hn) (g) {M a} (h) (h₁) (h₂)`), closed before `w4_box_returnedRows`.

## 6. Compile, axioms, checks

`cd work/lean && lake env lean ../drafts/corner/W5_ROW.lean` — **0 errors, exit 0, 43 s** (load ≈ 4-6); **exactly 8 `declaration uses
sorry`**: 4437 `s7q_box_ret`, 18053 `s7z_F_exists`, 18494 `s7z_returned_of_FSector` (the three superseded W3/K boxes, unchanged),
**20301 `w5r_box_transport`, 20309 `w5r_box_corners`, 20316 `w5r_box_contact`, 20324 `w5r_box_branch`** (this unit's four black boxes),
20419 `s7_bigon_law_at` (the leaf); no other warning.  `w4_box_returnedRows` (20334) is no longer sorried.
`#print axioms` (scratch copy `<scratchpad>/w5r/W5_ROW_axioms.lean` = the file + 19 print lines after `end SM`, 43 s):

| declaration | axioms |
|---|---|
| **`w5r_returnedRow_of`** | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — **no `sorryAx`** |
| `w5r_coef_spectator` | same (through `s7fc_coef_eq`) |
| `w5r_carrierWeight_e`, `w5r_e_qL`, `w5r_sgn_cast`, `w5r_sgn_ne_zero`, `w5r_prod_sub_prod`, `w5r_spectator_prod` | `[propext, Classical.choice, Quot.sound]` |
| **`w4_box_returnedRows`** | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — `sorryAx` through the four boxes ONLY |
| `w5r_box_transport` / `_corners` / `_contact` / `_branch` | `sorryAx` + standard (+ `lit_homfly`, `lp_lm` where the statement mentions coefficients/`cornerHomfly`) |
| `w4_s7_bigon_law_at_of`, `s7_sliding_law_at` | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` — no `sorryAx` (unchanged) |
| `s7_bigon_law_at`, `thm_C_S7_of`, `thm_C_S7` | `sorryAx` (the leaf's own `sorry`; unchanged lists) |

Frozen statements 5/5 PASS; clash scan clean; diff = 2 hunks (header §); `grep -c sorry` 16 → 19.

## 7. For the assembler

* Merge: pure insertion `19853a19854,20330` + body `19858c20335,20355` on `W4_Assembled.lean`; the block references only W4 material
  and the library (no other wave-5 unit's names), so it merges independently of RT/SITE/BR.
* Connecting the boxes: RT's deliverable → `w5r_box_transport` (+ `w5r_box_corners` if RT builds the merged corner correspondence);
  SITE's → `w5r_box_contact`; BR's → `w5r_box_branch` (one disjunct) and possibly `w5r_box_corners`.  If a unit delivers its data at
  carriers characterised differently (e.g. "the carrier owning `x`"), `owner_eq_iff`/`carrierCrossings_disjoint` identify them with
  `w5r_qH` (a visit has one owner; `x ∈ carrierCrossings q_H` pins `q_H`), and `firstHalf_zero`/`secondHalf_zero` identify the half
  contact carriers with `w5r_L₁`/`w5r_L₂`.  `turn` vs `principalTurn` in the corner data: the same `e`.
* Once the four boxes are proved: `w4_box_returnedRows` is sorry-free and the leaf closes by the one-line body of §4 (the assembler's
  step, merge rule); `thm_C_S7` then loses `sorryAx`.
* Reproduce: `cp W4_Assembled.lean W5_ROW.lean`; insert `<scratchpad>/w5r/block.lean` after line 19853; replace line 19858 (`  sorry`)
  by `<scratchpad>/w5r/body.lean` (`<scratchpad>/w5r/assemble` = the Python in this session's transcript, assert-guarded);
  `cd work/lean && lake env lean ../drafts/corner/W5_ROW.lean`.  Scratch: prefix olean `<scratchpad>/w5r/pfx/W5Prefix.olean`
  (W4 lines 1-19853 + closing `end`s, 54 s), wrapper `lean.sh`, harness `Test2.lean` (12 s per round).
* Timeline (UTC): 08:25 start (reports, W4 glue, BLOCK/J/K/SITE/SITEH/FB2/FB3 interfaces, sm-4:440-835); 08:37 prefix build; 08:45
  Test1; 08:49 Test2 clean; 08:52 `W5_ROW.lean` assembled; 08:55 full compile + axioms; 09:05 report.
