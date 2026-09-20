# W5_ASSEMBLY_REPORT — corner wave 5 (row 110 `thm:C-S7`) MERGE, 2026-09-19 11:20 UTC / 7:20am ET (under D-AUTH-20260919, no bound)

File: **`work/drafts/corner/W5_Assembled.lean`** (25,237 lines, sha256
`69b01559712ba9b79ed2d9f48f8ec84f99eae1d41ce90e365febff08ed95759d`) = `W4_Assembled.lean` (19,974 lines, `9c0ec3b7…`) + the
four wave-5 unit blocks VERBATIM (RT `w5t_` 2,599 lines, SITE `w5s_` 245, BR `w5b_` 1,656, ROW `w5r_` 477; 1,366 new declarations
against `Statements_FINAL.lean`, 338 more than W4) + the `w5_` assembly glue (7 declarations, 252 lines) + three body replacements
(ROW's boxes `w5r_box_transport`, `w5r_box_contact`; the W4 glue box `w4_box_returnedRows`).
`diff W4_Assembled.lean W5_Assembled.lean` = `1,6c1,8` (header) + `19853a19856,25096` (one insertion) + `19858c25101,25121`
(`  sorry` → 21-line body); the deleted side is the six W4 header lines and that one `  sorry`.
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W5_Assembled.lean`, 44 s): **0 errors, 0 warnings other than exactly
10 `declaration uses sorry`** — 4439 `s7q_box_ret`, 18055 `s7z_F_exists`, 18496 `s7z_returned_of_FSector` (W3/K, superseded),
23881 `w5b_box_returnedData` (BR, superseded by `w5_returnedData`, UNUSED), **24278 `w5b_box_interlacingTurnData`,
24287 `w5b_box_noninterlacingTurnData`, 24304 `w5b_box_curlData`, 25071 `w5r_box_corners` (the FOUR LIVE boxes)**, 25090
`w5r_box_branch` (ROW, restated as `w5_box_branch`, UNUSED), 25185 `s7_bigon_law_at` (the leaf, merge rule).  `grep -c sorry` = 22
= 10 bodies + 12 prose mentions (W4's 11 + this header).  `tools/stmt_check.py --base W3_Skeleton.lean` 5/5 PASS; `tail -n 43`
identical to `W3_Skeleton.lean`; `tools/clash_scan.py`: `duplicates_in_assembled: []`, `full_name_clashes: {}` (45 short-name
coincidences, all in different namespaces).  Nothing written under `work/lean`; `lake build` never run.

## 0. In one paragraph

**Prop B2' `w4_box_returnedRows` is PROVED MODULO FOUR OPEN GEOMETRIC BOXES; `thm_C_S7` is NOT sorry-free.**  Of ROW's four
consumed Props, two are DISCHARGED at assembly from RT and SITE (`w5r_box_transport` ← `w5_transportData`, `w5r_box_contact` ←
`w5_contactData`; both sorry-free), one is RESTATED under the live selector and discharged from BR modulo BR's three open boxes
(`w5_box_branch` — ROW's `w5r_box_branch` has no selector hypothesis, BR's turn and curl fields are stated under `wt(q_L) ≠ 0`,
and the row needs the branch data only there: `w5_returnedRow_of` handles `wt(q_L) = 0` directly), and one stays OPEN
(`w5r_box_corners`, the contact-corner correspondence, which neither RT nor BR delivered).  BR's consumed returned-transport
data is supplied by RT through `w5_returnedData` (BR's own box `w5b_box_returnedData` is stated without the contact-parameter
facts RT's transport needs, so it stays sorried and unused).  `#print axioms thm_C_S7` = `[propext, sorryAx, Classical.choice,
Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]`; the
`sorryAx` enters through the bigon leaf's own `sorry` (kept, merge rule), and would enter through exactly the four live boxes if
the leaf were wired.  **Wave 6 = the four boxes** (§6): a corner-correspondence unit (closes `w5r_box_corners` and, with glue,
the pattern fields), a rotation unit (BR's two turn boxes' `rotation` fields: A2's centre polygon `L*` + U110-I) and a curl
unit (`w5b_box_curlData`: cb:products on the one-curl component).  Not port-ready (§7).

## 1. Task (1): unit diffs against `W4_Assembled.lean` — all clean

`diff W4_Assembled.lean W5_<U>.lean` (verified 10:50Z): each unit file = `W4[1..19853]` + one block + `W4[19854..]`, inserted
immediately BEFORE the docstring of `w4_box_returnedRows` inside `section W4Bigon` (`variable (hn) (g) {M a} (h) (h₁) (h₂)`); the
deleted side is empty except ROW's one `  sorry`.  `stmt_check` 5/5 PASS and `tail -n 43` identical for all four; every top-level
name carries the unit prefix (nested: `w5t_ReturnedTransport.*` 44, `w5b_GaussSide.*` 19, `w5b_GaussSplit.*` 24); no unit added
an import, `open`, `attribute` or top-level `variable`; BR's clash scan (not in its report, agent died): duplicates `[]`, clashes `{}`.

| unit | prefix | hunks (W4 anchors) | block lines | sorried bodies added | body replaced |
|---|---|---|---|---|---|
| RT | `w5t_` | `19853a19854,22452` | 2,599 (146 decls) | none | none |
| SITE | `w5s_` | `19853a19854,20098` | 245 (20) | none | none |
| BR | `w5b_` | `19853a19854,21509` | 1,656 (137) | 4: `w5b_box_returnedData`, `_interlacingTurnData`, `_noninterlacingTurnData`, `_curlData` | none |
| ROW | `w5r_` | `19853a19854,20330` + `19858c20335,20355` | 477 (29) | 4: `w5r_box_transport`, `_corners`, `_contact`, `_branch` | `w4_box_returnedRows` (`  sorry` → 21 lines) |

## 2. Task (2): layout of `W5_Assembled.lean` (dependency order RT, SITE, BR, ROW; glue inside ROW's section before its boxes)

| W5 lines | content |
|---|---|
| 1-8 | assembly header (`--` comments) |
| 9-19855 | W4 lines 7-19853 verbatim (through `def w4_BigonReturnedRows`) |
| 19856-22454 | **RT** block verbatim (`w5t_qH` 20884, `namespace w5t_ReturnedTransport` 20958: `owner_inl_eq_qH_iff` 21029, `specEquiv` 21147, `firstCrossingQ_mem_carrierCrossings_iff` 21256; second namespace block 21717: `carrierWeight_first` 21885, `coef_first` 21910; `w5t_transport` 22116, `w5t_returned_terms` 22400) |
| 22455-22699 | **SITE** block verbatim (`w5s_site` 22600, `w5s_rotation` 22636, `w5s_ContactRowData_e` 22659, `w5s_exists_wall` 22675, `w5s_exists_contactRowData` 22683) |
| 22700-24355 | **BR** block verbatim (`w5b_ReturnedData` 23866, `w5b_box_returnedData` 23881, `w5b_v` 24073, `w5b_v_fst_val` 24082, `w5b_components_of_interlacing` 24124, `_of_not_interlacing` 24187, `w5b_qL` 24245, `w5b_InterlacingTurnData` 24250, `w5b_NoninterlacingTurnData` 24260, **boxes 24278, 24287**, `w5b_CurlData` 24294, **box 24304**, `w5b_interlacingData` 24321, `w5b_noninterlacingData` 24338) |
| 24356-24798 | **ROW** block, part 1 verbatim (`section W5Row`; `w5r_sgn` 24382, `w5r_qH` 24418, `w5r_qL` 24423, `w5r_x` 24438, `w5r_TransportData` 24515, `w5r_CornerData` 24544, `w5r_ContactData` 24575, `w5r_DifferentBlockData` 24586, `w5r_BranchData` 24618, `w5r_returnedRow_of` 24700, `end W5RowAt`) |
| **24799-25050** | **`w5_` glue `section W5Glue`** (§3): `w5_signType_cast_ne_zero` 24824, `w5_returnedData` 24842, `w5_transportData` 24854, `w5_contactData` 24917, `w5_branchData` 24935, `w5_returnedRow_of` 24969, `w5_box_branch` 25043 |
| 25052-25096 | ROW block, part 2 (the four boxes) verbatim except the bodies of **`w5r_box_transport` 25056 (proved, 8 lines)** and **`w5r_box_contact` 25078 (proved, 5 lines)**; `w5r_box_corners` 25071 and `w5r_box_branch` 25090 keep `sorry`; `end W5Row` |
| 25097-25100 | W4 19854-19857 verbatim (docstring + statement of `w4_box_returnedRows`) |
| **25101-25121** | **new body of `w4_box_returnedRows`** (§3.6; ROW's 21-line body is superseded — it consumed `w5r_box_branch`) |
| 25123-25237 | W4 19859-19974 verbatim (`w4_oneNewborn_rows`, `w4_s7_bigon_law_at_of` 25150, `end W4Bigon` 25175, the leaf `s7_bigon_law_at` 25185 with its `sorry` at 25194, `thm_C_S7_of` 25203, `thm_C_S7_of_floor` 25228, `thm_C_S7` 25233) — the last 43 lines byte-identical to `W3_Skeleton.lean` |

**Renames: none** (disjoint prefixes).  **Identifications used by the glue, all definitional or one-line:** `w5r_qH = w5t_qH … M = w5b_qH`
(each `owner … (Sum.inl M)`), `w5r_L₁ = w5t_L₁ = w5b_L₁`, `w5r_L₂ = …` (each `owner … (Sum.inl 0)`; `w5r_T₁`/`w5b_ι₁` are
`abbrev`s of RT's `s7b_pre (s7b_firstCrossingQ …) (lift T₀)`), `w5r_x = w5s_x` (both `carrierCrossingEquiv⁻¹ ⟨s7f_x, hx⟩`);
`w5r_qL = owner μ_M` on `P₀` vs `(s7fc_e …).symm q_H` (= SITE's shape, = `w5b_qL`): equal by ROW's `w5r_e_qL` through
`Equiv.symm_apply_eq` (two-line `hqL` in `w5_contactData`, `w5_branchData`).  **De-duplication: none applied** (W4 §2's content
duplicates plus, now, the triples `w5r_qH/w5t_qH/w5b_qH`, `w5r_L₁/w5t_L₁/w5b_L₁`, `w5r_x/w5s_x`, and the twin SignType facts
`w5r_sgn_ne_zero` / `w5_signType_cast_ne_zero`; to be collapsed at port).

### Black boxes connected / not connected

| box (unit) | producer | connected |
|---|---|---|
| `w5r_box_transport` (ROW ← W5-RT) | RT's `w5t_transport`, `specEquiv`, `carrierWeight_first/second`, `coef_first/second`, `w5t_carrierRotation_first/second`, `w5t_cutFirst_of/_cutSecond_of` via **`w5_transportData`** | **YES** — body replaced; `[propext, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness]`, no `sorryAx` |
| `w5r_box_contact` (ROW ← W5-SITE) | SITE's `w5s_ContactRowData_e` + `w5s_exists_wall` via **`w5_contactData`** | **YES** — body replaced; standard axioms only |
| `w5r_box_branch` (ROW ← W5-BR) | BR's `w5b_interlacingData` / `w5b_noninterlacingData` — but those require `wt(q_L) ≠ 0`, which ROW's Prop lacks | **NO as stated** (not derivable from BR; possibly false without the selector — CONJECTURE, not tested).  **RESTATED** as **`w5_box_branch`** (the same `∃ δ … ∀ T₀ ∈ EligDec, ∀ hT, wt(q_L) ≠ 0 → w5r_BranchData`), PROVED from BR modulo BR's boxes 2-4 via `w5_branchData`; the row consumes only this (`w5_returnedRow_of`).  `w5r_box_branch` stays sorried, UNUSED |
| `w5r_box_corners` (ROW ← RT or BR) | nobody: RT stated no corner list for `q_H` (W5_RT_REPORT §4 "not stated here"), BR's turn boxes assume the patterns rather than derive them | **NO — OPEN (wave 6, W6-COR)** |
| `w5b_box_returnedData` (BR ← W5-RT) | RT's `w5t_x_mem_qH`, `w5t_y_mem_qH`, `firstCrossingQ_mem_carrierCrossings_iff` + `owner_inl_eq_qH_iff` (and the `second` twins) via **`w5_returnedData`** | **In substance YES, in shape NO**: BR's box takes only `hloc : s7a2_IntervalLocal … r η δ`, `ht`, `hE`, but RT's `w5t_transport` needs `hr hr0 hr1 hη` (`g.center M = edgePoint … r`, `0 < r < 1`, `0 < η`), which `hloc` (`∀ u, |u| < δ → VertexLocalData …`) does not carry; so the box is not discharged and stays sorried, UNUSED; `w5_returnedData` (standard axioms) feeds BR's deliverables directly |
| `w5b_box_interlacingTurnData`, `w5b_box_noninterlacingTurnData`, `w5b_box_curlData` (BR) | none in wave 5 | **NO — OPEN (wave 6, W6-ROT / W6-COR glue / W6-CURL)** |
| `w4_box_returnedRows` (W4 glue, B2') | `w5_returnedRow_of` on the radii of `s7f_exists_bigonSplit`, `s7a2_exists_intervalLocal`, `w5r_box_transport`, `w5r_box_corners`, `w5r_box_contact`, `w5_box_branch` | **YES, modulo the four live boxes** (`sorryAx` through `w5r_box_corners` and BR's boxes 2-4 only) |
| `s7_bigon_law_at` (leaf) | `w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)` (sorry-free glue, W4 §4) | **NOT wired** (merge rule: the input is not sorry-free); closure line unchanged |

## 3. Task (2), the glue (`section W5Glue`, 24799-25050; variables `hn g {M a} h h₁ h₂` of `W4Bigon`; `section W5GlueAt` adds
`t T₀ {r η δ δ'} hloc hδ hr hr0 hr1 hη hηr hηr1 hdet ht ht'`, included per theorem)

1. **`w5_returnedData hn g h h₁ h₂ t T₀ hloc hr hr0 hr1 hη ht (hE : s7f_Eligible …) : w5b_ReturnedData hn g h h₁ h₂ t T₀`**
   (11 lines): `x_mem`/`y_mem` are RT's `w5t_x_mem_qH`/`w5t_y_mem_qH`; `first_mem`/`second_mem` are
   `hT.firstCrossingQ_mem_carrierCrossings_iff c _ _ (hT.owner_inl_eq_qH_iff hη hw)` (resp. `second`/`inr`) with
   `hT := w5t_transport …`, `hw := w5t_hw …`; `w5b_qH ≡ w5t_qH … M` and `w5b_L₁ ≡ w5t_L₁` unify by `exact`.
2. **`w5_transportData … hloc hδ hr hr0 hr1 hη hηr hηr1 hdet ht ht' hsplit hmem hT : w5r_TransportData hn g h h₁ h₂ t T₀ hT`**
   (60 lines): `e := (hT.specEquiv hη hw).symm`; for each clause, `obtain ⟨c, hc⟩ := (specEquiv).surjective q`, prove the clause
   at `specEquiv c` by `rcases c` (`carrierWeight_first/second h.1.2.1 hr hr0/hr1 hη hw hchi hT hT₁/hT₂ L hL`; `coef_first/second hη hw
   (w5t_split' … hsplit) hT hT₁' L hL (w5t_cutFirst_of/… hord hchi … L hrot.symm)` with `hrot := w5t_carrierRotation_first/second …` —
   the calls of RT's `w5t_spec_factor₁/₂` split into their weight and coefficient halves), then `subst hc; erw [hc']` with
   `hc' : specEquiv.symm q = c`.  `hT₁ hT₂` (needed by the WEIGHT clause, which ROW states without decomposition hypotheses) come
   from `w4_eligibleEquiv hsplit ⟨T₀, hmem⟩`, hence the `hsplit`/`hmem` arguments.
3. **`w5_contactData hn g h t T₀ hloc ht hW hT : w5r_ContactData hn g h t T₀ hT`** (10 lines): `w5s_ContactRowData_e … (w5r_qH …) hW hT hx hy`
   rewritten by `hqL : (s7fc_e …).symm (w5r_qH …) = w5r_qL …` (from `w5r_e_qL`); `w5s_x ≡ w5r_x` by `exact`.
4. **`w5_branchData … hloc hr hr0 hr1 hη hηr hηr1 ht hmem hT (hW : carrierWeight … (w5r_qL …) ≠ 0) : w5r_BranchData hn g h h₁ h₂ t T₀ hT`**
   (28 lines): `hRT := w5_returnedData …`; `hqL : w5b_qL … = w5r_qL …` (`unfold w5b_qL; Equiv.symm_apply_eq; w5r_e_qL`); the visit
   `v := w5b_v … hT hRT` with `hv : v.1 = w5r_x hT hx` (`(Equiv.eq_symm_apply _).mpr (Subtype.ext (w5b_v_fst_val …))`); the smoothing
   diagram from the LIBRARY's `exists_smoothing_record_visit (positiveLift …) (w5r_x …) v hv` (`SM/Smoothing.lean`; `DA`, `ι`); then
   `w5b_interlacingData … hI hW' DA ι` → `⟨v, DA, i, j, hv, hb⟩` after `rw [hqL] at hb`, and `w5b_noninterlacingData … hI hW' DA ι` →
   `Or.inl ⟨v, DA, i, j, hv, Or.inl hb⟩` (the first, `L₁`-curl orientation of ROW's `ε = 0` disjunction; the swapped orientation and
   the different-block alternative are not used).
5. **`w5_returnedRow_of hn g h h₁ h₂ t T₀ hloc ht hF hsplit hmem hRT hCC hSITE (hBR : wt(q_L) ≠ 0 → w5r_BranchData …) : ⟨ROW's row⟩`**
   (62 lines): `by_cases hW : carrierWeight … (w5r_qL …) = 0`.  If not, ROW's `w5r_returnedRow_of … (hBR hW)`.  If so:
   `wt(q_H) = 0` (`← w5r_e_qL`, `← w5r_carrierWeight_e`), hence `term₂(T) = 0` and `term₀(T₀) = 0` (`s7e_term_of_decomposition`,
   `unfold wind`, `Finset.prod_eq_zero`); for `ε = 1` the corner data (`hCC`) and `s7c_carrierWeight_interlacing` give
   `0 = −s₀ · wt(L₁) wt(L₂)` with `(s₀ : ℤ) ≠ 0` (`w5_signType_cast_ne_zero (w5r_sgn_ne_zero g h t)`), so `wt(L₁) = 0 ∨ wt(L₂) = 0`
   and the corresponding half term vanishes; for `ε = 0` the right side is `0 · …`; `ring`.  **No black box is consumed here.**
6. **`w5_box_branch hn g h h₁ h₂ : ∃ δ > 0, ∀ t < δ, ∀ T₀ ∈ w4_EligDec, ∀ hT, wt(q_L) ≠ 0 → w5r_BranchData … hT`** (A2's radius +
   `w5_branchData`), and the **new body of `w4_box_returnedRows`** (25101-25121) = ROW's composition with `w5r_box_branch` →
   `w5_box_branch` and `w5r_returnedRow_of` → `w5_returnedRow_of` (radii `min (min δ₁ δ₂) (min (min δ₃ δ₄) (min δ₅ δ₆))` of
   `s7f_exists_bigonSplit`, `s7a2_exists_intervalLocal`, `w5r_box_transport`, `w5r_box_corners`, `w5r_box_contact`, `w5_box_branch`).
   The bodies of **`w5r_box_transport`** (25056; `s7f_exists_bigonSplit`, `s7a2_exists_intervalLocal` with its `r η` facts,
   `s7fb_exists_detRadius hn g h hloc hr hr1 hδ₂`, then `w5_transportData`) and **`w5r_box_contact`** (25078; A2's radius,
   `w5s_exists_wall`, then `w5_contactData`) replace ROW's `sorry`s.

Compiled on the second probe against a prefix olean (W4[1..19853] + the four blocks, `<scratchpad>/w5asm/pfx/W5AsmPrefix.olean`,
47 s to build, 12 s per probe; `Probe2.lean`), then in place.  Two compile-fix rounds, both mechanical and both the same issue:
`rw [Equiv.symm_apply_apply]` and `rw [hc']` fail to find `e.symm (e c)` because the coercion's implicit domain is ROW's
`{q // q ≠ w5r_qH …}` on one side and RT's `{q // q ≠ w5t_qH … M}` on the other (equal only by unfolding two `def`s; the target is
"not type-correct under `implicit` transparency" — every `h.1.1` of a `BigonAt` is) → `erw` with the closed equation `hc'`.
Also `exact_mod_cast` does not know `SignType` casts → `cases s <;> simp_all` (`w5_signType_cast_ne_zero`).

## 4. Task (3): compile, axioms, frozen statements, clash scan

Compile: §header.  `#print axioms` (scratch copy `<scratchpad>/w5asm/W5_Assembled_axioms.lean` = the file + 34 `#print axioms SM.<name>`
lines after `end SM`, 45 s, log `axioms.log`; standard = `propext`, `Classical.choice`, `Quot.sound`; registered literature axioms
`lit_homfly`, `lit_homfly_descent`, `lp_lm`, `lp_lm_uniqueness`, `ng_finite_word`, `src_contact`):

| declaration | sorryAx | other axioms | sorryAx source |
|---|---|---|---|
| **`thm_C_S7`** | **YES** | standard + all six literature | **exactly one: the body of `s7_bigon_law_at`** |
| `thm_C_S7_of_floor`, `thm_C_S7_of` | YES | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | the bigon leaf |
| `s7_sliding_law_at` | no | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — (closed, W4) |
| `s7_bigon_law_at` | YES (own `sorry`) | standard + `lit_homfly` | — |
| `w4_s7_bigon_law_at_of` | no | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — |
| **`w4_box_returnedRows`** (B2') | **YES** | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | **the four live boxes only** (`w5r_box_corners`; BR's 24278, 24287, 24304 through `w5_box_branch`) |
| **`w5_returnedRow_of`**, `w5r_returnedRow_of`, **`w5_transportData`**, **`w5r_box_transport`**, `w5t_returned_terms` | **no** | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — |
| **`w5_contactData`**, **`w5r_box_contact`**, **`w5_returnedData`**, `w5t_transport`, `w5t_returnedTransport_of`, `w5s_ContactRowData_e`, `w5s_exists_contactRowData`, `w5b_components_of_interlacing`, `w5b_components_of_not_interlacing` | **no** | standard only | — |
| `w5_box_branch`, `w5_branchData`, `w5b_noninterlacingData` | YES | standard + `lit_homfly`, `lp_lm` | BR's boxes 24278/24287/24304 |
| `w5b_interlacingData` | YES | standard | BR's box 24278 |
| `w5r_box_corners` (LIVE), `w5b_box_interlacingTurnData` (LIVE), `w5b_box_noninterlacingTurnData` (LIVE), `w5b_box_returnedData` (dead) | YES (own) | standard | — |
| `w5b_box_curlData` (LIVE) | YES (own) | standard + `lit_homfly`, `lp_lm` | — |
| `w5r_box_branch` (dead) | YES (own) | standard + `lit_homfly`, `lp_lm` | — |
| `s7q_box_ret`, `s7z_F_exists`, `s7z_returned_of_FSector` (dead, W3/K) | YES (own) | standard (+ `lit_homfly`) | — |

No unregistered axiom appears anywhere.  Frozen statements: `python3 tools/stmt_check.py W5_Assembled.lean --base W3_Skeleton.lean`
→ 5/5 byte-identical and unique (PASS); `tail -n 43` identical to `W3_Skeleton.lean`.  Clash scan: §header.  Verbatim check
(each block located in `W5_Assembled.lean` and compared line by line, `<scratchpad>/w5asm/` verification script): RT, SITE, BR
verbatim; ROW verbatim except the glue inserted after `end W5RowAt` and the two `  sorry` lines replaced; W4 lines 7-19853 and
19854-19857, 19859-19974 verbatim.

## 5. Honest state: NOT sorry-free — the exact remaining Props

`thm_C_S7` carries `sorryAx`.  Wiring the leaf would move the source to exactly these FOUR declarations (statements as in the
file; `hP₂ := s7f_hP₂ g M a t`, `hP₀ := s7f_hP₀ g M a t`, `T := s7f_lift hn g h t T₀`, `T₁ := w5r_T₁ = s7b_pre ι₁ T`, `T₂ := w5r_T₂`,
`q_H := w5r_qH = owner hn hP₂ T (inl M)` (= `w5b_qH`), `q_L := w5r_qL = owner hn hP₀ T₀ (inl M)` (= `w5b_qL = (s7fc_e …).symm q_H`),
`L₁ := w5r_L₁ = owner … h₁ T₁ (inl 0)` (= `w5b_L₁`), `L₂ := w5r_L₂`, `s₀ := w5r_sgn g M a` with `(s₀ : ℤ) = s7f_dirSign · contactSign`,
`ccp := ccpCornerPolygon`):

1. **`w5r_box_corners` (25071, ROW; `w5r_CornerData` 24544)**: `∃ δ > 0, ∀ t < δ, ∀ T₀ ∈ w4_EligDec hn g h t,`
   `∃ (j : ZMod (ccpCornerCount q_H)) (j₁ : ZMod (ccpCornerCount L₁)) (j₂ : ZMod (ccpCornerCount L₂)) (e : {i // i ≠ j₁} ⊕ {i // i ≠ j₂} ≃ {i // i ≠ j}),`
   `(∀ x, turn (ccp q_H) (e x).1 = Sum.elim (fun y => turn (ccp L₁) y.1) (fun y => turn (ccp L₂) y.1) x) ∧ turn (ccp L₁) j₁ = s₀ ∧ turn (ccp L₂) j₂ = s₀ ∧`
   `turn (ccp q_H) j = (if s7f_Interlacing hn h t then s₀ else -s₀)`.
2. **`w5b_box_interlacingTurnData` (24278, BR; `w5b_InterlacingTurnData` 24250)**: `∀ t T₀ {r η δ} (hloc) (ht : t < δ) (hT₀ : IsDecomposition hn hP₀ T₀)
   (hS₁ : IsDecomposition … T₁) (hS₂ : … T₂), s7f_Interlacing hn h t → carrierWeight hn hP₀ T₀ (w5b_qL … hloc ht) ≠ 0 →`
   `|carrierRotationInt hn hP₀ T₀ q_L| = |carrierRotationInt … L₁| + |carrierRotationInt … L₂| ∧ SignedUniformOrOneDissent (ccp L₁) ∧ SignedUniformOrOneDissent (ccp L₂)`.
3. **`w5b_box_noninterlacingTurnData` (24287; `w5b_NoninterlacingTurnData` 24260)**: same hypotheses with `¬ s7f_Interlacing`,
   conclusion `|R(L₁)| + |R(L₂)| − |R(q_L)| = −1 ∧ SignedUniformOrOneDissent (ccp L₁) ∧ SignedUniformOrOneDissent (ccp L₂)`.
4. **`w5b_box_curlData` (24304; `w5b_CurlData` 24294)**: `∀ t T₀ {r η δ} hloc ht (hS₁ : IsDecomposition … T₁) (DA : Diagram) (i : Fin DA.Γ.c),`
   `Nonempty (RecordIso (DA.knotRestrict i).record (CB.gaussRecord (CB.cg hn hP₂) (insert (s7f_y hn h t) (s7b_img (s7b_firstCrossingQ_injective …) (carrierCrossings … L₁))))) →`
   `SM.P (DA.knotRestrict i) = cornerHomfly … T₁ L₁ hS₁ ∧ (DA.knotRestrict i).writhe = (carrierCrossingCount … T₁ L₁ : ℤ) + 1`.

Dead (sorried, on no proved path; drop at port): `w5r_box_branch` (25090; superseded by `w5_box_branch`), `w5b_box_returnedData`
(23881; superseded by `w5_returnedData`), `s7q_box_ret` (4439), `s7z_F_exists` (18055), `s7z_returned_of_FSector` (18496).

## 6. Wave 6 — the four boxes as named units (same shape as W4 §5; all consumed interfaces are PROVED)

The turn boxes 2 and 3 decompose: their `pattern₁/₂` fields follow from box 1's corner data by U110-C (`s7c_uniform_halves_of_interlacing`
/ `s7c_dissent_halves_of_noninterlacing`: from `e, he, hj, hj₁, hj₂` and `wt(q_H) ≠ 0` — `wt(q_H) = wt(q_L)` by `w5r_carrierWeight_e` +
`w5r_e_qL` — they give `∀ i, turn (ccp q_H) i = ±s₀`, the two half patterns, and `s7c_signedUniformOrOneDissent_of_forall`), so
only their `rotation` fields need new geometry.  For those, U110-I's `s7i_carrierRotationInt_interlacing/_noninterlacing` want the
correspondence `e` to preserve PRINCIPAL turns (angles), which holds EXACTLY only when both polygons live on the same tuple:
the halves' corner polygons live on the centre `g.center`, `ccp q_H` on `P₂(t)`.  BR's design (docstrings 24272-24292) is A2's
centre polygon `L*` — the corner-polygon family of `q_H` through the wall (`s7a2_cornerFamily`, regular for `|u| ≤ t` since every
corner mark of `q_H` is persistent, `s7fc_hSp'`; `w5s_rotation`'s argument) evaluated at `u = 0`, whose principal turns ARE those of
`L₁ ⊔ L₂` with the contact corner; `s7i_full_rotation_germ_centre` transports `rotationNumber` from `P₂(t)` to the centre, and
`w5s_rotation` (SITE, proved) carries `|R(q_H)| = |R(q_L)|`.

| wave-6 unit | Prop (per eligible decomposition `T₀`, below a radius) | interfaces instantiated (all proved) | est. lines |
|---|---|---|---|
| **W6-COR** (contact-corner correspondence; closes **`w5r_box_corners`**) | `w5r_CornerData hn g h h₁ h₂ t T₀` (§5.1): the corner list of `q_H` is the merge of the corner lists of `L₁` and `L₂` cut at their vertex-`0` corners with `μ_M` inserted, turn-preserving off the three contact corners; `turn (ccp L₁) j₁ = turn (ccp L₂) j₂ = s₀` at the halves' vertex `0` (sm-4:576-600, eq. s7c:angle-orders: λ₁ turns `E_a → E_M`, λ₂ turns `E_{M−1} → E_a`, both of sign `s₀ = δ_dir·s`); `turn (ccp q_H) j = ±s₀` at `μ_M` by `ε` (the turn `E_{M−1} → E_M` of `P₂(t)`: sign `sgn sin(β − α + π)`, `+s₀` iff `x_a < y_a` iff interlacing — `s7o_interlaces_iff`, `s7fb_ya_lt_xa_of_not_interlaces` give the parameter order, `s7fb_turn_eq`/`s7fb_crossingSign_centre`/`s7fb_chi_eq` the sign bookkeeping) | RT's `w5t_transport` (`hT.ret : s7b_ReturnTransport σ_T (w5t_glued g₁ g₂ (inl 0) (inl 0)) w5t_mark`, the owner lemmas `hT.owner_inl_eq_qH_iff`, `hT.owner_xl/_yl/_xa/_ya`), RT's abstract corner transport `w5t_ct_*` (Part D; to be extended from "one cycle ↦ one cycle up to shift" to "two cycles glued at their vertex-0 marks ↦ one cycle with `μ_M` inserted": `w5t_ct_cornerMark_succ`, `w5t_ct_mem_cornerList_iff`, `w5t_ct_cornerList_rotated` patterns on the glued first-return), RT's `w5t_markTurn_first/second` (turns of image marks = turns of half marks), `ccp_corner_chain`, `ccpCornerMark_*`, `s7a_isTrueCorner_persistent`, `s7fb_persistent_of_edge_*`, `s7f_pattern`, `w5r_sgn_cast`/`s7f_s₀_eq_chi` | 700-1,100 |
| **W6-ROT** (rotation fields of BR's boxes 2 and 3) | `w6_RotationData`: `|R(q_H)| = |R(L₁)| + |R(L₂)|` if `ε = 1`, `|R(L₁)| + |R(L₂)| − |R(q_H)| = −1` if `ε = 0`, under `wt(q_H) ≠ 0` (then `|R(q_L)|` by `w5s_rotation`, SITE — or directly `w5r_ContactData`'s `rotation` field) | A2's corner-polygon family of `q_H` (`s7a2_cornerFamily`, `s7a2_cornerFamily_side_self`, `s7a2_point_eq_evaluation`, `s7a2_carrierRotation_eq`'s own regularity argument for the contact carrier — SITE's `w5s_rotation` shows the family is regular through the wall), `s7i_full_rotation_germ_centre` (rotation constant along a regular family), the centre polygon `L*` (its principal turns: those of `ccp L₁`, `ccp L₂` off vertex `0` — same points on `g.center` — plus the turn at `g.center M`), U110-I `s7i_interlacing_absolute` / `s7i_noninterlacing_absolute` on `L*`, `L₁`, `L₂` with W6-COR's `e`, `he` (principalTurn form, exact on the centre), `s7c_uniform_halves_of_interlacing` / `s7c_dissent_halves_of_noninterlacing` for `hall/hrest` (from W6-COR + `wt(q_H) ≠ 0`); `rotationNumber_of_reindexed`, `Reindexed` for the corner shift | 600-1,000 |
| **W6-CURL** (closes **`w5b_box_curlData`**) | `w5b_CurlData hn g h h₁ t T₀ hS₁ DA i` (§5.4) for any `DA i` with the record clause: `P(DA_i) = H⁺_{L₁}`, `writhe(DA_i) = m₁ + 1` | BLOCK's `s7k_curl_component_value` / `s7k_curl_component_writhe` (block supplies `C` for the record `gaussRecord (insert y (img ι₁ X_{L₁}))` — the curl `y` an isolated one-crossing block `H₀` of value `1`, writhe `1`: its two occurrences are adjacent, `w5b_y_visits`/`w5b_keptFinset_B_eq_of_not`, so `y` interlaces nothing — and `C'` for the positive lift of `L₁` with `e : {H ≠ H₀} ≃ blocks'`, `he` equal block values), cb:products `cb_products … .product` (`CbProductsData`, SM/CBProducts.lean) on `T₁`'s carrier `L₁` through `CB.positiveLiftRecordIso` / U110-D's Gauss-record transport (BR's `w5b_gaussIso₁`), `CB.gaussRecord` interlacement-graph components, `Record.writhe` counting | 500-900 |
| **W6-GLUE** (assembler) | bodies of `w5r_box_corners` (← W6-COR), `w5b_box_interlacingTurnData` / `_noninterlacingTurnData` (← W6-COR's `e he hj hj₁ hj₂` + `s7c_*_halves_*` for the patterns, W6-ROT + `w5s_rotation`/`w5r_carrierWeight_e` for `rotation`), `w5b_box_curlData` (← W6-CURL); then `w4_box_returnedRows` is sorry-free and the leaf closes as `w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)` | — | 100-200 |

**Total ≈ 1,900-3,200 lines.**  Order: W6-COR first (W6-ROT's `e` and BR's pattern fields read it); W6-ROT and W6-CURL in
parallel; each unit follows the S1P pattern on `W5_Assembled.lean` (pure insertion inside `section W4Bigon` before the docstring of
`w4_box_returnedRows`, or, for W6-COR, the body of `w5r_box_corners` replaced), so that the merge replaces exactly one body per
unit.  Note for W6-COR/W6-ROT: the turn boxes' hypothesis is `wt(q_L) ≠ 0` in BR's `w5b_qL` spelling (`(s7fc_e …).symm q_H`);
`w5_branchData`'s `hqL` converts to `w5r_qL` and `w5r_carrierWeight_e … hT₀ q_L` + `w5r_e_qL` to `wt(q_H) ≠ 0`.

## 7. Task (4): port — NOT ready

`thm_C_S7` carries `sorryAx` (§4), so `work/drafts/corner/port/CS7/` is not prepared and no prose/docstring rewording or
de-duplication was applied (W4 §7's list still stands).  Additions to that list for the port once wave 6 closes the four boxes:
drop `w5r_box_branch` (with nothing depending on it) and `w5b_box_returnedData` (idem); collapse `w5r_qH/w5t_qH/w5b_qH`,
`w5r_L₁/w5t_L₁/w5b_L₁`, `w5r_L₂/…`, `w5r_x/w5s_x`, `w5r_T₁/w5t_T₁/w5b_ι₁`-preimages, `w5r_sgn_ne_zero`/`w5_signType_cast_ne_zero`
(keep ROW's names); reword the "BLACK BOX" docstrings of `w5r_box_transport`, `w5r_box_contact` (proved here), of
`w4_box_returnedRows` (kept verbatim in this merge for byte-identity of W4's glue) and, after wave 6, of the four live boxes; the
`w5_` glue and `w5_returnedRow_of` go into `SM/CS7Units.lean` verbatim with the units (split RT/BR into their own module if the
units file exceeds ~90 s: the whole file compiles in 44 s now, so one module is likely fine).

## 8. Deviations and assembler's edits, disclosed

1. **The bigon leaf is NOT wired** although the task text says to close it: the merge rule of W3/W4/ROW (a frozen leaf's body is
   replaced only by a sorry-free term) applies since B2' still carries `sorryAx`; the closure line is unchanged and recorded in the
   header.  Frozen statement byte-identical either way.
2. **ROW's body of `w4_box_returnedRows` (its 21 lines) is superseded by the assembler's 21-line body** (§3.6): ROW's consumed
   `w5r_box_branch` and `w5r_returnedRow_of`, whose branch input is not derivable from BR's deliverables (§2 table); the new body is
   ROW's with two names changed.  The diff against W4 therefore still deletes only `  sorry` there.
3. **The glue is inserted INSIDE ROW's block** (`section W5Row`, after `end W5RowAt`, before the four boxes; 24799-25050), because two
   of ROW's boxes receive bodies that call the glue and Lean needs the glue first; ROW's block is otherwise verbatim (the S1P
   precedent of W4 §3).  The glue uses only `W4Bigon`'s variables and its own `W5GlueAt` variables.
4. **Two unit boxes are left sorried and unused** rather than proved: `w5r_box_branch` (ROW) — its Prop lacks the selector hypothesis
   under which BR states the turn/curl fields (whether it is false without the hypothesis is untested; CONJECTURE: the pattern
   fields fail for a dead contact carrier) — and `w5b_box_returnedData` (BR) — its hypotheses do not carry `hr hr0 hr1 hη`.  Both are
   discharged in restated shape (`w5_box_branch`, `w5_returnedData`) and both are draft material to drop at port.  They add two to
   the `declaration uses sorry` count (10 instead of 8).
5. **The `ε = 0` orientation**: `w5_branchData` supplies ROW's FIRST `s7k_NoninterlacingData` disjunct (curl on `L₁`'s component),
   as BR proves it; ROW's swapped orientation and different-block alternative are unused (they remain in ROW's Prop verbatim).
6. **`w5_returnedRow_of`'s dead-selector case is new mathematics of the assembly** (≈35 lines, no box): it is what makes the
   selector hypothesis of BR's shape harmless for Prop B2'.  Checked: `[propext, Classical.choice, Quot.sound, lit_homfly, lp_lm,
   lp_lm_uniqueness]`.
7. Header: W4's six comment lines replaced by eight (`1,6c1,8`).  No frozen text, no unit docstring, no import touched.  The
   reassessment rule was not triggered (two mechanical compile-fix rounds on one issue, §3).

## 9. Verification record

```
cd work/lean && lake env lean ../drafts/corner/W5_Assembled.lean        # 0 errors; 10 × "declaration uses sorry" (4439 18055 18496 23881 24278 24287 24304 25071 25090 25185); 44 s
cd work/lean && lake env lean <scratchpad>/w5asm/W5_Assembled_axioms.lean  # the 34 #print axioms lines of §4; 45 s
python3 work/drafts/corner/tools/stmt_check.py work/drafts/corner/W5_Assembled.lean --base work/drafts/corner/W3_Skeleton.lean   # 5/5 PASS
python3 work/drafts/corner/tools/clash_scan.py work/drafts/corner/W5_Assembled.lean   # duplicates [] / full_name_clashes {} / 1366 new decls
diff work/drafts/corner/W4_Assembled.lean work/drafts/corner/W5_Assembled.lean | grep '^[0-9]'   # 1,6c1,8  19853a19856,25096  19858c25101,25121
for u in RT SITE BR ROW; do diff W4_Assembled.lean W5_$u.lean | grep '^[0-9<]'; done      # 19853a19854,<end> each; ROW + 19858c20335,20355, deleted `  sorry`
grep -c sorry W5_Assembled.lean   # 22 (10 bodies + 12 prose)
```
Reproduce the merge: `<scratchpad>/w5asm/assemble.py` (assert-guarded; inputs `header.lean`, `glue.lean`, `body_transport.lean`,
`body_contact.lean`, `body_rows.lean`); probes `Probe1.lean` (signatures), `Probe2.lean` (the glue + the three bodies as test
theorems) against `pfx/W5AsmPrefix.olean` via `lean.sh`.  Timeline (UTC): 10:44 start (reports, unit diffs, RT/SITE/BR/ROW
interfaces, BLOCK/SITE/library statements); 10:46 executor's BR report received; 10:58 prefix olean; 11:02 Probe1; 11:05 Probe2
(2 rw failures) → 11:08 clean; 11:09 assembled, full compile 0 errors (44 s); 11:12 axioms, stmt/clash/verbatim checks; 11:20 report.
