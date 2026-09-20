# W3_ASSEMBLY_REPORT — corner wave 3 merge (row 110 thm:C-S7), 2026-09-15 22:35 UTC / 6:35pm ET

Merge assembler.  Inputs: `W3_Skeleton.lean` (97 lines) + the eight unit files `W3_{SPLIT,RET,ROT,F,SITE,BLOCK,J,K}.lean` with
their reports.  Output: **`work/drafts/corner/W3_Assembled.lean`** — 8,958 lines, sha256
`109050d918ecd5371c8a79f699aaa52bbb6100425925ffbcb5a163e56883736f`, **0 errors, 0 non-sorry warnings, 12 `declaration uses sorry`**
(`cd work/lean && lake env lean ../drafts/corner/W3_Assembled.lean`, 26 s, exit 0).  Nothing written under `work/lean`; the
`#print axioms` run used a scratch copy in the session scratchpad (`lake env lean <abs path>` from `work/lean`).

**Bottom line.** Both leaves stay open.  `thm_C_S7` compiles but carries `sorryAx` through both leaves.  TWO of ROT's four
sliding boxes are closed at assembly: `s7q_box_split` by unit SPLIT (`s7p_exists_pivotSplit`) and `s7q_box_order` by unit RET
(`s7r_first_order`/`s7r_second_order` at the germ data `s7r_hord`) — both now sorry-free.  The remaining inputs are FIVE named
Props — two sliding, three bigon — each leaf with a sorry-free `w3_<leaf>_of : Props → leaf statement`:
`w3_s7_sliding_law_at_of₂ (hret : w3_SlidingRet) (hcar : w3_SlidingCarriers)` (the three-Prop form `w3_s7_sliding_law_at_of`
with `hord : w3_SlidingOrder` is kept; S2 is proved as `w3_SlidingOrder_of_box`) and
`w3_s7_bigon_law_at_of (hFs : w3_BigonFSector) (hR : w3_BigonReturnedRows) (hO : w3_BigonOneNewborn)`.  Not port-ready.

## 1. Task (1): unit diffs against the skeleton — all clean

`diff W3_Skeleton.lean W3_<U>.lean` hunks (pure insertions except K's leaf body):

| unit | prefix | hunk | block lines in unit file | anchor | frozen text changed |
|---|---|---|---|---|---|
| SPLIT | `s7p_` | `22a23,1240` | 23-1240 (1,218) | before `s7_sliding_law_at` docstring | none |
| RET | `s7r_` | `22a23,2203` | 23-2203 (2,181) | same | none |
| ROT | `s7q_` | `22a23,1277` | 23-1277 (1,255) | same | none |
| F | `s7f_` | `36a37,1140` | 37-1140 (1,104) | before `s7_bigon_law_at` docstring | none |
| SITE | `s7s_` | `36a37,1105` | 37-1105 (1,069) | same | none |
| BLOCK | `s7k_` | `36a37,769` | 37-769 (733) | same | none |
| J | `s7j_` | `36a37,509` | 37-509 (473) | same | none |
| K | `s7z_` | `36a37,608` + `54c626` | 37-608 (572) | same | ONLY the bigon leaf's `sorry` → `exact s7z_bigon_law_at_of hn h h₁ h₂ (s7z_exists_rowSector hF hsing hn h h₁ h₂)` (allowed by rule (2)) |

Every block is a balanced set of `section … end` groups inside `section VertexEdge`; no unit added an import, a top-level
`variable`, or an `open` at the `VertexEdge` level (SITE's `open GeoCarrier RProof` are inside its sub-sections).  454
declarations in the eight blocks; every top-level name carries its unit's prefix (the 28 unprefixed names live inside
`namespace s7r_SlidingTransport'` / `namespace s7f_BigonSplit`, so their full names are prefixed); no name occurs twice.

## 2. Task (2): layout of `W3_Assembled.lean`

| lines | content |
|---|---|
| 1-6 | assembly header (prose only) |
| 7-23 | skeleton 6-22 verbatim: the four imports, `namespace SM`, `open Link Carrier`, `attribute [local instance] Classical.propDecidable`, `noncomputable section`, `section VertexEdge`, `variable {n : ℕ} [NeZero n]` |
| 24-1240 | **SPLIT** block verbatim (`section S7PSplit` … `end S7PSplit`; `s7p_exists_pivotSplit` at 1176) |
| 1242-3421 | **RET** block verbatim (`s7r_slidingTransport_side` / `_side'` in `section S7RGerm`, ends 3420) |
| 3423-4686 | **ROT** block, verbatim except two boxes: `s7q_box_split` (line 4367; docstring reworded "DISCHARGED at assembly by unit SPLIT", body `sorry` → `obtain ⟨δ, hδ, hs⟩ := s7p_exists_pivotSplit hn g h h₁ h₂; exact ⟨δ, hδ, fun t ht => ⟨(hs t ht).1, (hs t ht).2⟩⟩`; `s7q_Split` unfolds to SPLIT's `s7b_PivotSplit`, accepted by defeq) and `s7q_box_order` (line 4470; docstring "DISCHARGED at assembly by unit RET", body `sorry` → the 9-line proof of §3.1: `s7a2_exists_intervalLocal` for `r hr hr0 hr1`, `hz := h.1.2.1`, `unfold s7q_OrderAgrees`, `(s7r_first_order hn h.1.1 hz h.1.2.2.2.1 hr hr0 (s7e_hQC hn g h t b) (s7r_hord hn g h hloc t ht b) v w he).symm` and the `s7r_second_order` twin with `hr1`) |
| 4689-4839 | **`section W3Sliding`** (glue, §3 below) |
| 4841-4852 | skeleton 23-34 verbatim: `s7_sliding_law_at` (body `sorry`) |
| 4855-5957 | **F** block verbatim |
| 5959-7025 | **SITE** block verbatim |
| 7028-7759 | **BLOCK** block verbatim |
| 7761-8231 | **J** block verbatim |
| 8234-8804 | **K** block verbatim (its §E boxes kept as sorried theorems) |
| 8807-8896 | **`section W3Bigon`** (glue, §3 below) |
| 8898-8915 | skeleton 37-54 verbatim: `s7_bigon_law_at` (body `sorry` — the skeleton's, NOT K's composition; K's composition is available as `s7z_bigon_law_at_of hn h h₁ h₂ (s7z_exists_rowSector hF hsing hn h h₁ h₂)` and adds nothing sorry-free) |
| 8916-8958 | skeleton 55-97 verbatim: `end VertexEdge`, `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7`, `end`, `end SM` |

Order: producers before consumers — SPLIT before ROT (ROT's `s7q_box_split` now calls `s7p_exists_pivotSplit`); RET before
ROT (ROT's `s7q_box_order` now calls RET's `s7r_first_order`/`s7r_second_order`/`s7r_hord`; the `ret` box cannot consume RET yet, §3.1); F, SITE, BLOCK, J before K (K references none of them; the glue
references K only).  **Renames: none needed.  De-duplication: none needed** (disjoint prefixes; K's `s7z_side`/`s7z_x`/`s7z_y`
duplicate F's `s7f_side`/`s7f_x`/`s7f_y` definitionally but under different names — both kept, as K's report allows).

### Black boxes connected / not connected

| box (unit) | producer available? | connected |
|---|---|---|
| `s7q_box_split` (ROT) | YES — `s7p_exists_pivotSplit` (SPLIT), statement identical after unfolding `s7q_Split` | **YES, sorry-free** |
| `s7q_box_ret` (ROT) | PARTIAL — RET proved `s7r_slidingTransport_side` (`s7b_SlidingTransport` on the leg-`(M−1)` side at `s7e_vl`) and `s7r_slidingTransport_side'` (the CORRECTED `s7r_SlidingTransport'` on the leg-`M` side at `s7e_va`).  ROT's box demands `s7b_SlidingTransport` on BOTH sides with `vm.1 = x∓`; W3_RET_REPORT §2 proves this is FALSE on the leg-`M` side | NO — kept as **Prop S1** `w3_SlidingRet` (see §3.1) |
| `s7q_box_order` (ROT) | YES — RET's `s7r_first_order`/`s7r_second_order` ARE the box's law per side (iff reversed), with `hord := s7r_hord hn g h hloc t ht b` and `hz hr hr0 hr1` from `s7a2_exists_intervalLocal` (RET's own germ recipe in `s7r_slidingTransport_side`) | **YES, sorry-free** (**Prop S2** `w3_SlidingOrder` PROVED: `w3_SlidingOrder_of_box`) |
| `s7q_box_carriers` (ROT) | NO producer (ROT's own remaining geometry (a)-(c)) | NO — **Prop S3** `w3_SlidingCarriers` |
| `s7z_F_exists` (K) | NO — F's three boxes are themselves sorried, and F's proved output (`s7f_law_residual`) has a different shape (K §4(a)/(b): 200-400-line bridge) | NO — **Prop B1** `w3_BigonFSector` |
| `s7z_returned_of_FSector` (K) | NO — SITE/BLOCK/J prove the row content on explicit hypotheses; per-support instantiation open | NO — **Prop B2** `w3_BigonReturnedRows` |
| `s7z_oneNewborn_exists` (K) | NO | NO — **Prop B3** `w3_BigonOneNewborn` |
| `s7f_exists_bigonSplit`, `s7f_exists_twoNewbornTerm`, `s7f_exists_ineligible_transport` (F) | no producer | kept sorried (F's own §2 geometry; feed `s7f_exists_law_residual`, off the leaf path) |
| `s7s_clear_local`, `s7s_wallTriangleData_of_bigon` (SITE) | no producer | kept sorried (they feed `s7s_siteData_of_wall`, off the leaf path) |

## 3. Task (3): the leaves and the `w3_` glue

Both leaves keep the skeleton's `sorry`: their inputs are not all proved.  The glue names the remaining inputs EXACTLY (the
box statements verbatim, extracted programmatically from the unit files) and proves the leaf statements from them, sorry-free.

### 3.1 Sliding (`section W3Sliding`, lines 4689-4839; `variable (hn) (g) {M a} (h : g.SlidingAt M a)`)

| declaration | line | what |
|---|---|---|
| `def w3_SlidingRet hn g h h₁ h₂ : Prop` | 4705 | **Prop S1** = statement of `s7q_box_ret` |
| `def w3_SlidingOrder hn g h : Prop` | 4726 | **Prop S2** = statement of `s7q_box_order` (`∃ δ>0, ∀ t<δ, ∀ b, s7q_OrderAgrees hn g h t b`) — **PROVED** |
| `def w3_SlidingCarriers hn g h h₁ h₂ : Prop` | 4730 | **Prop S3** = statement of `s7q_box_carriers` |
| `w3_SlidingRet_of_box`, `w3_SlidingCarriers_of_box` | 4758, 4764 | shape checks `s7q_box_* : w3_Sliding*` (typecheck by defeq; carry `sorryAx`; not on any `w3_*_of` path) |
| **`w3_SlidingOrder_of_box : w3_SlidingOrder hn g h := s7q_box_order hn g h`** | 4762 | **S2 PROVED, sorry-free** (axioms: standard only) |
| `theorem w3_box_rows_of hn g h h₁ h₂ (hret : S1) (hcar : S3) (hord : S2) : <s7q_box_rows statement>` | 4768 | ROT's `s7q_box_rows` with its boxes as hypotheses (proof = ROT's, first three `obtain`s on the hypotheses) — sorry-free |
| **`theorem w3_s7_sliding_law_at_of hn g h h₁ h₂ (hret : w3_SlidingRet hn g h h₁ h₂) (hord : w3_SlidingOrder hn g h) (hcar : w3_SlidingCarriers hn g h h₁ h₂) : <s7_sliding_law_at statement>`** | 4809 | proof = ROT's `s7q_exists_contactSector` (with the now-proved `s7q_box_split`) + `s7e_sliding_law_at_of_contact` — **sorry-free** |
| **`theorem w3_s7_sliding_law_at_of₂ hn g h h₁ h₂ (hret : w3_SlidingRet hn g h h₁ h₂) (hcar : w3_SlidingCarriers hn g h h₁ h₂) : <s7_sliding_law_at statement>`** | 4829 | `:= w3_s7_sliding_law_at_of … hret (s7q_box_order hn g h) hcar` — **the two-Prop form, sorry-free** |

**Sizes / status of S1-S3.**
* **S1 `w3_SlidingRet`** — NOT provable as stated (W3_RET_REPORT §2, rule 4): on the side carrying `{a, M}` the mark map
  `s7b_slidingMark` sends `inl (inl 0) ↦ μ_M` and `inr (inl 0) ↦ v_ℓ`, but `nextMark μ_M = v_ℓ` there, so `ret` fails for every
  `vm`.  RET's correct output for that side is `s7r_SlidingTransport'` (mark map `swap(μ_M, v_a) ∘ s7b_slidingMark … v_a`,
  proved with the full `componentEquiv` / `carrierCrossings_eq_img_*` / `carrierCrossingCount_eq_*` toolkit in
  `namespace s7r_SlidingTransport'`).  What closes the sliding leaf is therefore NOT S1 but a RESTATED S1' in which the leg-`M`
  side carries `s7r_SlidingTransport'` at `s7e_va` (the leg-`(M−1)` side stays `s7b_SlidingTransport` at `s7e_vl`;
  `s7e_leg g M a` decides which of `false`/`true` is which), together with a second copy of ROT's transport section
  (`s7q_CarrierData`, `s7q_rowData_of_transport`, `s7q_cutFirst_of/_cutSecond_of`, `s7q_coef_first/_second`, lines 3968-4346 ≈
  380 lines) on `s7r_SlidingTransport'`, and the glue `vm.1 = s7e_xm/xp` ↔ `s7e_vl`/`s7e_va` (W3_RET_REPORT §3, ~100 lines).
  Estimate: 500-700 lines, all consuming PROVED material (`s7r_slidingTransport_side`, `_side'`, `s7r_img_of_decomposition`
  for `hSimg`, `s7q_pre_of_symm` for the half supports).
* **S2 `w3_SlidingOrder`** — **PROVED at assembly** (9 lines): RET had already done the U_S7B parameter-law glue as
  `s7r_first_order`/`s7r_second_order` (`s7r_firstVisitQ_eq : s7b_firstVisitQ … v = s7a_visit hQC (s7b_firstHalfVisit … v) _` by
  `rfl`, then `hord` and the cut-edge rescaling `s7b_visitParameter_firstHalfVisit_cut`); the germ data `hz hr hr0 hr1 hord` are
  RET's own `s7r_slidingTransport_side` recipe (`s7a2_exists_intervalLocal`, `s7r_hord`).
* **S3 `w3_SlidingCarriers`** — ROT (a)-(c): ordered corner correspondence 400-600, `hbit` 150-250, `hr` exact 150-250, `hr`
  perturbation 300-500, turn-sign constancy 200-300, contact-sign memberships + `τ` 100-150 (ROT §6): **1,300-2,050 lines**,
  and it too must be restated on `s7r_SlidingTransport'` for the leg-`M` side (its `hT` arguments are `s7b_SlidingTransport`).

Sliding leaf remaining total ≈ **1,800-2,750 lines** (S1' 500-700 + S3 1,300-2,050), with the S1/S3 restatement on
`s7r_SlidingTransport'` for the leg-`M` side a prerequisite for consuming RET's `ret`.

### 3.2 Bigon (`section W3Bigon`, lines 8807-8896; `variable {g} {M a}`)

| declaration | line | what |
|---|---|---|
| `def w3_BigonFSector hn h h₁ h₂ : Prop` | 8824 | **Prop B1** = conclusion of `s7z_F_exists` (∃ persistent `e₀`, eligible `e`, `s7z_FSector … e₀ e` below a radius) |
| `def w3_BigonReturnedRows hn h h₁ h₂ : Prop` | 8841 | **Prop B2** = conclusion of `s7z_returned_of_FSector` (its hypothesis `hF : FloorTheoremData` does not occur in the conclusion) |
| `def w3_BigonOneNewborn hn h : Prop` | 8859 | **Prop B3** = conclusion of `s7z_oneNewborn_exists` (`hsing` likewise absent from the conclusion) |
| `w3_BigonFSector_of_box`, `w3_BigonReturnedRows_of_box hF`, `w3_BigonOneNewborn_of_box hsing` | 8864-8873 | shape checks (carry `sorryAx`) |
| **`theorem w3_s7_bigon_law_at_of hn h h₁ h₂ (hFs : w3_BigonFSector hn h h₁ h₂) (hR : w3_BigonReturnedRows hn h h₁ h₂) (hO : w3_BigonOneNewborn hn h) : <s7_bigon_law_at statement>`** | 8876 | proof = K's `s7z_exists_rowSector` on the hypotheses + `s7z_bigon_law_at_of` — **sorry-free** |

Note the frozen leaf's `hF`, `hsing` enter only as hypotheses of B2, B3: `s7_bigon_law_at hF hsing … := w3_s7_bigon_law_at_of hn h h₁ h₂
(B1-proof) (B2-proof hF) (B3-proof hsing)` once the three exist.

**Sizes / status of B1-B3** (from the unit reports).
* **B1 `w3_BigonFSector`** — F's three boxes (`s7f_exists_bigonSplit` 600-900, `s7f_exists_twoNewbornTerm` 1,000-1,500,
  `s7f_exists_ineligible_transport` 500-800) plus the F→K shape bridge of W3_K_REPORT §4(b) (200-400): **2,300-3,600 lines**.
  Alternatively K's F-ALIGNED route `s7z_bigon_law_at_of_residual` consumes F's PROVED `s7f_law_residual` directly (K §4(a) recipe,
  verified shape-identical) and needs only `hrow`/`hone` per eligible `T₀` and the eligible bijection restricted to F's filter
  (200-400) — that route replaces B1 by F's three boxes and moves the row obligations into F's vocabulary.
* **B2 `w3_BigonReturnedRows`** — the per-support instantiation of SITE (`s7s_siteData_of_wall` — itself still on
  `s7s_clear_local` 300-450 + `s7s_wallTriangleData_of_bigon` 300-500 + `hrec` 1,000-1,650), BLOCK (`s7k_ContactRowData` /
  `s7k_InterlacingData` / `s7k_NoninterlacingData` interfaces: Gauss-record identifications, `R_H = R_L` through the wall),
  ROT (rotation ledger), RET, J (floor entries `s7j_*_entry` at the half contact carriers): W3_BLOCK_REPORT §2 estimates
  **3,500-5,400 lines**; the polynomial/row algebra is PROVED on hypotheses (`s7k_switch_value`, `s7k_skein_on`, `s7k_extraction`,
  `s7k_component_value`, `s7j_interlacing_entry`, `s7j_noninterlacing_entry`, `s7j_below_floor_entry` — all sorry-free, §4).
* **B3 `w3_BigonOneNewborn`** — J's cb:singleton entry with C's one-newborn selectors on F's split vocabulary: **400-700 lines**.

Bigon leaf remaining total ≈ **6,200-9,700 lines** (SITE's own 1,600-2,600 included in B2).

## 4. Task (4): compile and `#print axioms`

Compile: 0 errors; the 12 `declaration uses sorry` are exactly the 12 sorried bodies (`grep -c sorry` = 20 = 12 bodies + 8 prose):
`s7q_box_ret` 4437, `s7q_box_carriers` 4519, `s7_sliding_law_at` 4844, `s7f_exists_bigonSplit` 5371,
`s7f_exists_twoNewbornTerm` 5388, `s7f_exists_ineligible_transport` 5725, `s7s_clear_local` 6972, `s7s_wallTriangleData_of_bigon`
7018, `s7z_F_exists` 8600, `s7z_returned_of_FSector` 8620, `s7z_oneNewborn_exists` 8639, `s7_bigon_law_at` 8906.
(`s7q_box_split` and `s7q_box_order` no longer warn.)

`#print axioms` (scratch copy = the file + `#print axioms SM.<name>` lines after `end SM`, two runs, 55 + 28 names; standard = `propext`,
`Classical.choice`, `Quot.sound`; literature = the registered `SM.lit_homfly`, `SM.lit_homfly_descent`, `SM.lp_lm`,
`SM.lp_lm_uniqueness`, `SM.ng_finite_word`, `SM.src_contact` of `axiom-policy.json`):

| declaration | sorryAx | other axioms | through which boxes |
|---|---|---|---|
| **`thm_C_S7`** | **YES** | standard + all six literature (the `thm_floor` chain adds `lit_homfly_descent`, `ng_finite_word`, `src_contact`) | both leaves |
| `thm_C_S7_of_floor` | YES | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | both leaves |
| `thm_C_S7_of` | YES | standard + `lit_homfly` | both leaves |
| `s7_sliding_law_at` (leaf) | YES (own `sorry`) | standard + `lit_homfly` | — |
| `s7_bigon_law_at` (leaf) | YES (own `sorry`) | standard + `lit_homfly` | — |
| **`w3_s7_sliding_law_at_of`**, **`w3_s7_sliding_law_at_of₂`** | **no** | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — |
| **`w3_box_rows_of`** | **no** | same | — |
| **`w3_s7_bigon_law_at_of`** | **no** | standard + `lit_homfly` | — |
| `w3_Sliding{Ret,Carriers}_of_box` | YES | standard | `s7q_box_ret` / `s7q_box_carriers` |
| **`w3_SlidingOrder_of_box`**, **`s7q_box_order`**, `s7r_first_order`, `s7r_second_order`, `s7r_hord` | **no** | standard | — (S2 closed) |
| `w3_Bigon{FSector,ReturnedRows,OneNewborn}_of_box` | YES | standard + `lit_homfly` | `s7z_F_exists` / `s7z_returned_of_FSector` / `s7z_oneNewborn_exists` |
| **`s7q_box_split`**, `s7p_exists_pivotSplit` | **no** | standard | — (SPLIT's whole chain sorry-free) |
| `s7p_sliding_law_at_of_hterm` | no | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — |
| `s7q_box_rows`, `s7q_exists_contactSector`, `s7q_sliding_law_at_of_boxes` | YES | same | `s7q_box_ret`, `s7q_box_carriers` |
| `s7q_hterm_of_rows`, `s7q_rowData_of_carrierData` | no | standard + `lit_homfly` (+ `lp_lm`, `lp_lm_uniqueness` for the latter) | — |
| `s7r_slidingTransport_side`, `s7r_slidingTransport_side'`, `s7r_img_of_decomposition` | no | standard | — (RET's whole chain sorry-free) |
| `s7z_bigon_law_at_of`, `s7z_law_at_of_rowSector`, `s7z_bigon_law_at_of_residual`, `s7z_law_at_of_residual` | no | standard + `lit_homfly` | — |
| `s7z_exists_rowSector` | YES | standard + `lit_homfly` | K's three boxes |
| `s7f_law_residual`, `s7f_law_decomposition` | no | standard + `lit_homfly` | — |
| `s7f_exists_law_residual` | YES | standard + `lit_homfly` | F's three boxes |
| `s7s_core`, `s7s_site`, `s7s_contact_sign` | no | standard | — |
| `s7s_siteData_of_wall` | YES | standard | `s7s_clear_local` |
| `s7k_switch_value`, `s7k_skein_on`, `s7k_extraction` | no | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — |
| `s7k_component_value` | no | standard + `lp_lm` | — |
| `s7j_interlacing_entry`, `s7j_noninterlacing_entry`, `s7j_below_floor_entry` | no | standard | — |

Every non-standard axiom on every path is a registered literature axiom; no unregistered axiom appears anywhere.

## 5. Task (5): frozen statements and name clashes

* **Byte identity**: for each of `s7_sliding_law_at`, `s7_bigon_law_at`, `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7`, the segment
  docstring + statement + body in `W3_Assembled.lean` is byte-identical to the skeleton's (Python line-list comparison; also
  `diff <(sed -n 55,97p W3_Skeleton.lean) <(tail -n 43 W3_Assembled.lean)` is empty).  Both leaf bodies are the skeleton's `sorry`.
* **Name clash scan**: 475 top-level names in the assembled file = 454 (units) + 16 (`w3_`) + 5 (frozen), no duplicates
  (`sort | uniq -d` empty).  Against `work/lean` (namespace `SM`, all `SM/*.lean`, plus `RProof`, `CV`, `Bridge`, `Supplemental`):
  `grep -rE "\b(s7r_|s7p_|s7q_|s7f_|s7s_|s7k_|s7j_|s7z_|w3_)"` over `work/lean/SM` → **0 hits** (the prefixes are new to the
  library); every unit name carries its prefix, the unprefixed ones are namespace-qualified (`s7r_SlidingTransport'.componentEquiv`
  etc.).  The compile itself is the definitive check: the file imports the whole ported library and elaborated with 0 errors, so no
  new name shadows or collides with a library declaration in namespace `SM`.

## 6. Task (6): port plan — NOT port-ready

`thm_C_S7` carries `sorryAx`, so no `port/CS7/` was prepared.  **Honest state for FINAL_REVIEW** (also in `port/CS7_STATE.md`):

> **Row 110 thm:C-S7: both leaves open, 5 named Props remaining.**  `SM.thm_C_S7 : CS7Data` compiles as `thm_C_S7_of_floor thm_floor`
> with `thm_C_S7_of hF hsing` proved from the two branch leaves, but `s7_sliding_law_at` and `s7_bigon_law_at` are `sorry`.
> Sorry-free reductions exist: `w3_s7_sliding_law_at_of₂ : w3_SlidingRet → w3_SlidingCarriers → leaf` and
> `w3_s7_bigon_law_at_of : w3_BigonFSector → w3_BigonReturnedRows → w3_BigonOneNewborn → leaf` (`W3_Assembled.lean` lines 4829,
> 8876).  Sizes: sliding ≈ 1,800-2,750 lines (S1 must first be RESTATED on the leg-`M` side with RET's corrected
> `s7r_SlidingTransport'` — the current `s7q_box_ret` is false as stated there, 500-700; S3 1,300-2,050; S2 is PROVED); bigon ≈
> 6,200-9,700 lines (B1 2,300-3,600 incl. F's three geometric boxes; B2 3,500-5,400 incl. SITE's 1,600-2,600; B3 400-700).
> Proved and sorry-free in wave 3, ready to port with the leaves later: SPLIT entire (`s7p_exists_pivotSplit`), RET entire
> (`s7r_slidingTransport_side`, `_side'`), ROT's angle/merge/algebra/transport sections, `s7q_box_split` and `s7q_box_order`, F's
> `s7f_law_residual`/`s7f_law_decomposition`, SITE's `s7s_core`/`s7s_site`/`s7s_contact_sign` + wall-field lemmas, BLOCK's row
> theorems, J's floor entries, K's row algebra — 10 of the 12 sorries are the five Props' suppliers (2 ROT, 3 F, 2 SITE, 3 K), plus one per leaf.
> Axioms on `thm_C_S7`: standard + the six registered literature axioms + `sorryAx`; nothing unregistered.

When the five Props land, the port is mechanical: `SM/CS7Units.lean` = lines 24-8804 of `W3_Assembled.lean` with the two glue
sections (imports `SM.CornerChainUnits SM.CS7Sliding SM.BigonDeletion SM.CarrierFloorRows`; the 8 prose `sorry` mentions —
`grep -n sorry` minus the 12 bodies — to be reworded), `SM/CS7.lean` = the two leaves (bodies `w3_s7_sliding_law_at_of₂ … S1 S3`,
`w3_s7_bigon_law_at_of … B1 (B2 hF) (B3 hsing)`), `thm_C_S7_of`, `thm_C_S7_of_floor`, `theorem thm_C_S7 : CS7Data :=
thm_C_S7_of_floor thm_floor`.  `port/tools/port_build.py` / `port_clash_scan.py` / `port_stmt_check.py` from the wave-2a port apply.

## 7. Notes for the next wave (order of attack)

1. **Sliding, S1'/S3 restatement (prerequisite, ~150 lines of statements + the ~380-line transport section copied onto
   `s7r_SlidingTransport'`)**: split `s7q_box_ret`/`s7q_box_carriers`/`s7q_box_rows` by `s7e_leg g M a`; on the leg-`(M−1)` side
   instantiate `s7r_slidingTransport_side` (needs `hSimg` = `s7r_img_of_decomposition … hsplit hS hx` and `(s7e_vl hc).1 = x∓`),
   on the leg-`M` side `s7r_slidingTransport_side'` with a `s7q_CarrierData'` on `s7r_SlidingTransport'.componentEquiv`.  W3_RET_REPORT
   §3 gives the exact `hc`/`hl` case split.  After this, RET is fully consumed.
2. ~~S2~~ done at assembly (`s7q_box_order`).
3. **S3** geometry (ROT §6 list), 1,300-2,050 — restated on `s7r_SlidingTransport'` for the leg-`M` side together with S1'.
4. **Bigon**: prefer K's F-ALIGNED route (`s7z_bigon_law_at_of_residual` on `s7f_law_residual`): then the obligations are F's
   three boxes + `hrow`/`hone` per eligible `T₀` in F's vocabulary + the 200-400-line eligible-bijection restriction — no B1 bridge.
   B2's row content is proved (`s7k_*`, `s7j_*`) and waits on the SITE/BLOCK per-support identifications.
5. K's composition line for the bigon leaf (its `54c626`) was NOT carried into the assembled file (the leaf keeps `sorry` per the
   merge rule); re-apply it — or rather the `w3_s7_bigon_law_at_of` form — when B1-B3 exist.

Reproduce: `python3 <scratchpad>/assemble.py` (kept in the session scratchpad; slices the unit files by the ranges of §1, applies the
two box replacements (`s7q_box_split`, `s7q_box_order`) with `assert`-guarded string matches, extracts the six box statements
verbatim, writes the file).  Timeline: 22:17 UTC start, 22:25 first clean compile (13 sorries), 22:32 S2 closed (12), 22:35 report.
