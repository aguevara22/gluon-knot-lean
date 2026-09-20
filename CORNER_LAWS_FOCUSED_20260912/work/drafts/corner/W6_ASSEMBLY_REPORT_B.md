# W6_ASSEMBLY_REPORT_B — corner wave 6 (row 110 `thm:C-S7`) MERGE, assembly B, 2026-09-19 12:52 UTC / 8:52am ET (under D-AUTH-20260919, no bound)

**Assembly B.** Two W6-GLUE assembler instances ran on the same unit files (the W5 precedent `W5_Assembled_B.lean`); this is the
independent second one.  Its outputs carry the `_B` suffix — **`W6_Assembled_B.lean`**, this report, **`port/CS7_B/`** — so that the
other instance's `W6_Assembled.lean` / `W6_ASSEMBLY_REPORT.md` / `port/CS7/` are never touched (§8.1 discloses the one scratch-directory
collision).

File: **`work/drafts/corner/W6_Assembled_B.lean`** (27,531 lines, sha256 `3726574202bb1b676a9b637f7213abfad113373bcdf4be9442cd4cf233661ae2`) = `W5_Assembled.lean` (25,237 lines,
`69b01559712ba9b7…`) + the wave-6 unit blocks VERBATIM (CURL `w6k_` 357 lines, COR `w6c_` 436, ROT `w6r_` 530 with CC's `w6x_` 784
inserted inside it as in `W6_CC.lean`) + the two unit body replacements (COR's 9-line body of `w5r_box_corners`, CC's 9-line body of
`w6r_box_centreCorners`) + the `w6_` assembly glue (6 theorems, 165 lines, `section W6Glue`) + three one-line body edits (§3.4) +
the wired bigon leaf.  `diff W5_Assembled.lean W6_Assembled_B.lean | grep '^[0-9]'` = `1,8c1,12` (header) `24298a24302,24658` (CURL)
`24351c24711` (the `hcurl` line of `w5b_noninterlacingData`) `25067a25428,25863` (COR) `25073c25869,25877` (COR's body)
`25096a25901,27390` (ROT + CC + glue) `25106c27400` (`w5_box_branch` → `w6_box_branch` in `w4_box_returnedRows`) `25194c27488` (the leaf's
`  sorry` → the recorded closure line); the deleted side is the eight W5 header lines and those three one-liners.
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W6_Assembled_B.lean`, 58-62 s over three runs): **0 errors, 0 warnings other than exactly 8
`declaration uses sorry`** — 4442 `s7q_box_ret`, 18058 `s7z_F_exists`, 18499 `s7z_returned_of_FSector` (W3/K), 23884 `w5b_box_returnedData`,
24281 `w5b_box_interlacingTurnData`, 24290 `w5b_box_noninterlacingTurnData`, 24664 `w5b_box_curlData` (BR), 25894 `w5r_box_branch` (ROW) —
**all eight on no proved path** (§4).  **The bigon leaf `s7_bigon_law_at` no longer warns; `#print axioms thm_C_S7` =
`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word,
SM.src_contact]` — exactly the nine registered axioms, NO `sorryAx`.**  `grep -c sorry` = 20 = 8 bodies + 12 prose mentions.
`tools/stmt_check.py --base W3_Skeleton.lean` 5/5 PASS; `tail -n 43` identical to `W3_Skeleton.lean`; `tools/clash_scan.py`:
`duplicates_in_assembled: []`, `full_name_clashes: {}` (1,448 new declarations; 46 short-name coincidences, all in other namespaces).
Nothing written under `work/lean`; `lake build` never run.  **Port prepared: `work/drafts/corner/port/CS7_B/`** (§7).

## 0. In one paragraph

**Row 110 is CLOSED in the draft: `thm_C_S7 : CS7Data` is sorry-free on the nine registered axioms.**  Wave 6 delivered the last four
geometric inputs: COR proved ROW's `w5r_box_corners` (contact-corner correspondence), ROT proved both rotation identities per
`(t, T₀)` from the corner data and a centre-corner correspondence in principal-turn form (its one new box `w6r_box_centreCorners`),
CC proved that box, and CURL proved the curl component in the corrected form `w6k_box_curlData` (six radius facts added; the box as
stated, from `hloc ht` alone, is not derivable — W6_CURL_REPORT §2).  BR's two turn boxes are stated for EVERY side parameter `t`
and cannot be discharged as stated (the corner and centre data hold below radii only); exactly as ROW's `w5r_box_branch` in wave 5,
they are left unproved and UNUSED, and the glue restates the chain under the wave-6 radii: `w6_interlacingTurnData` /
`w6_noninterlacingTurnData` (BR's turn-field structures from ROT's `w6r_rotation_*` and U110-C's patterns on COR's data),
`w6_interlacingData` / `w6_noninterlacingData` (BR's deliverables with the two hypotheses `hCC hL`, CURL's corrected box in the
`ε = 0` body), `w6_branchData` / `w6_box_branch` (the wave-5 glue on `hCC hL`, radius = A2's ∧ `w5r_box_corners`' ∧
`w6r_box_centreCorners`').  `w4_box_returnedRows` consumes `w6_box_branch` in place of `w5_box_branch` and is sorry-free, so the leaf
closes by the recorded line `w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)`.  The nineteen
declarations still carrying `sorryAx` are all draft material off every proved path; they and seven sorry-free companions that only
serve them are dropped in the port (§7).

## 1. Task (1): unit diffs against `W5_Assembled.lean` — all clean

`diff W5_Assembled.lean W6_<U>.lean | grep '^[0-9<]'` (verified 12:10Z); `tools/stmt_check.py --base W3_Skeleton.lean` 5/5 PASS and
`tail -n 43` identical to `W3_Skeleton.lean` for every unit file; `tools/clash_scan.py`: `duplicates_in_assembled: []`,
`full_name_clashes: {}` for every unit file (45 short-name coincidences, all in other namespaces, as in W5); every new top-level name
carries the unit prefix; no unit added an import, `open`, `attribute` or top-level `variable`.

| unit | prefix | hunks (W5 anchors) | block lines | new decls | body replaced |
|---|---|---|---|---|---|
| COR | `w6c_` | `25067a25068,25503` + `25073c25509,25517` | 436 (10) | `w5r_box_corners` (`  sorry` → 9 lines) | — |
| ROT | `w6r_` | `25096a25097,25627` | 530 (20; one new sorried box `w6r_box_centreCorners`) | none | — |
| CURL | `w6k_` | `24298a24299,24655` | 357 (11) | none (`w5b_box_curlData` NOT replaced; corrected form `w6k_box_curlData`) | — |
| CC | `w6x_` | `25590a26035,26819` + `25597c26826,26834` against `W6_ROT.lean` | 784 (33) | `w6r_box_centreCorners` (`  sorry` → 9 lines) | — |

CC's file `W6_CC.lean` = `W5_Assembled.lean` + COR's two changes (byte-identical to `W6_COR.lean` up to `end W5Row`) + ROT's block with
CC's insertion(s) and the one body; verified by `diff W6_ROT.lean W6_CC.lean` = COR's two hunks + `25590a26035,26819` (the `w6x_` block inside `section W6Rot`, before the box) + `25597c26826,26834` (the body).

## 2. Task (2): layout of `W6_Assembled_B.lean`

| lines | content |
|---|---|
| 1-12 | assembly header (`--` comments) |
| 13-24301 | W5 lines 9-24298 verbatim |
| 24302-24658 | **CURL** block verbatim (`section W6CurlRecord` 24311-24479, `section W6Curl` 24481-24657; `w6k_box_curlData` 24574) |
| 24659-24710 | W5 24299-24350 verbatim (`w5b_box_curlData` 24664 keeps `sorry`; `w5b_interlacingData` 24681; `w5b_noninterlacingData` 24698) |
| **24711** | `  have hcurl := w6k_box_curlData hn g h h₁ t T₀ hloc ht hS₁ hr0 hr1 hr hη hηr hηr1 DA i hc₁` (was `w5b_box_curlData … hc₁`; the executor's re-thread) |
| 24712-25427 | W5 24352-25067 verbatim (ROW's block, the `w5_` glue: `w5_branchData` 25295, `w5_box_branch` 25403) |
| 25428-25862 | **COR** block verbatim (`section W6Cor … end W6Cor`) |
| 25863-25868 | W5 25068-25072 verbatim (docstring + statement of `w5r_box_corners` 25867) |
| 25869-25877 | COR's body of `w5r_box_corners` (9 lines) |
| 25878-25900 | W5 25074-25096 verbatim (`w5r_box_contact`, `w5r_box_branch` 25894, `end W5Row`) |
| 25901-27223 | **ROT** block with **CC** inside, verbatim from `W6_CC.lean` 25541-26863: `section W6Rot` 25901, `section W6RotAt` 26058-26393, **`section W6CC` 26395-27178** (`w6x_centreCornerData` 27136), `w6r_box_centreCorners` 27184 with CC's body, `w6r_exists_rotation` 27199, `end W6Rot` 27223 |
| **27225-27389** | **`w6_` glue `section W6Glue`** (§3): `section W6GlueAt` 27246-27329 (`w6_interlacingTurnData` 27258, `w6_noninterlacingTurnData` 27272, `w6_interlacingData` 27292, `w6_noninterlacingData` 27312), `section W6GlueBranch` 27331-27371 (`w6_branchData` 27341), `w6_box_branch` 27376 |
| 27391-27399 | W5 25097-25105 verbatim (docstring + statement of `w4_box_returnedRows` 27394, first five `obtain`s) |
| **27400** | `  obtain ⟨δ₆, hδ₆, hBR⟩ := w6_box_branch hn g h h₁ h₂` (was `w5_box_branch`) |
| 27401-27487 | W5 25107-25193 verbatim (`w4_s7_bigon_law_at_of` 27444, `end W4Bigon` 27469, the leaf's docstring + statement 27479-27487) |
| **27488** | `  exact w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)` (was `  sorry`) |
| 27489-27531 | W5 25195-25237 verbatim (`end VertexEdge` 27491, `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7` 27527) — the last 43 lines byte-identical to `W3_Skeleton.lean` |

Order: CURL before its box (the corrected form is consumed inside `w5b_noninterlacingData`, which follows the box); COR before
ROT (ROT/CC call `w5r_box_corners`); ROT (with CC) before the glue; the glue before `w4_box_returnedRows`.  **Renames: none**
(disjoint prefixes `w6k_ w6c_ w6r_ w6x_ w6_`).  **De-duplication: none applied** (§7.3).

## 3. Task (2): the glue (`section W6Glue`, 27225-27389; variables `hn g {M a} h h₁ h₂` of `W4Bigon`; 6 theorems, 165 lines)

**Why a restatement and not the boxes' bodies.** `w5b_box_interlacingTurnData` / `w5b_box_noninterlacingTurnData` quantify over
EVERY `t : g.SideParameter` (binders `t T₀ {r η δ} hloc ht hT₀ hS₁ hS₂ hI hW`) with no radius, whereas both inputs — COR's
`w5r_CornerData` (through `w5r_box_corners`) and the centre data `w6r_CentreCornerData` (through `w6r_box_centreCorners`) — exist only
below radii.  So the boxes cannot be given bodies as stated (the same obstruction as ROW's `w5r_box_branch` in W5 §2, resolved the same
way): they stay unproved and UNUSED, and the consuming chain is restated with the two data as hypotheses down to the point where a
radius can be intersected.  ROT's radius form `w6r_exists_rotation` (both identities under BR's binders) is sorry-free after CC but is
not used: the per-`(t, T₀)` theorems `w6r_rotation_interlacing` / `w6r_rotation_noninterlacing` are called directly with `hCC hL`, and the
two radii are intersected once, in `w6_box_branch`.

`section W6GlueAt` (variables `t T₀ {r η δ} hloc ht hT₀ hS₁ hS₂`, then `hT hRT hr0 hr1 hr hη hηr hηr1` — BR's `W5BRData` order, so the
binder orders of the restated deliverables mirror BR's):
1. **`w6_interlacingTurnData hn g h h₁ h₂ t T₀ hloc ht hT₀ hS₁ hS₂ hI hW hCC hL : w5b_InterlacingTurnData hn g h h₁ h₂ t T₀ hloc ht`**
   (`include hloc ht hT₀ hS₁ hS₂`): `rotation := w6r_rotation_interlacing … hI hW hCC hL`; `pattern₁/₂ :=
   s7c_signedUniformOrOneDissent_of_forall _ (w5r_sgn_ne_zero g h t) hall₁/₂` with `⟨-, hall₁, hall₂⟩ := w6r_patterns_interlacing … hI hW' hCC`,
   `hW' := w6r_weight_qH … hT₀ hW` (`wt(q_L) ≠ 0 → wt(q_H) ≠ 0`).  The fields are stated on `w5b_L₁ … / _` and the patterns come on
   `w5r_L₁ … (w5r_T₁ …)`; they unify by `exact` (definitional, as W5 §2 recorded).
2. **`w6_noninterlacingTurnData … hI hW hCC hL : w5b_NoninterlacingTurnData …`**: `rotation := w6r_rotation_noninterlacing … hI hW hCC hL`;
   the patterns are the last two conjuncts of `s7c_dissent_halves_of_noninterlacing hn _ … j j₁ j₂ (w5r_sgn_ne_zero g h t) hj hj₁ hj₂ e he hW'`
   on the destructured corner data (`hj` reduced by `simp only [hI, ↓reduceIte]`; `hCC` re-packed for the rotation call).
3. **`w6_interlacingData … hloc ht hT₀ hS₁ hS₂ hT hRT hr0 hr1 hr hη hηr hηr1 hI hW hCC hL DA ι : ∃ i j, s7k_InterlacingData … DA i j`** and
   **`w6_noninterlacingData … : ∃ i j, s7k_NoninterlacingData … DA i j`** = BR's `w5b_interlacingData` / `w5b_noninterlacingData`
   (statements verbatim plus `hCC hL`) with `have hturn := w6_*TurnData … hI hW hCC hL` in place of the box call and, at `ε = 0`,
   `have hcurl := w6k_box_curlData hn g h h₁ t T₀ hloc ht hS₁ hr0 hr1 hr hη hηr hηr1 DA i hc₁` (CURL's corrected form; the six radius
   facts are section variables here as in BR).
4. `section W6GlueBranch` (variables `t T₀ {r η δ} hloc ht hr0 hr1 hr hη hηr hηr1`): **`w6_branchData … hloc ht hr0 hr1 hr hη hηr hηr1 hmem hT hCC hL hW :
   w5r_BranchData hn g h h₁ h₂ t T₀ hT`** = `w5_branchData` verbatim with `hCC hL` threaded into the two calls.
5. **`w6_box_branch hn g h h₁ h₂ : ∃ δ > 0, ∀ t < δ, ∀ T₀ ∈ w4_EligDec, ∀ hT, wt(q_L) ≠ 0 → w5r_BranchData … hT`** (the statement of
   `w5_box_branch`): radius `min δ₁ (min δ₂ δ₃)` of `s7a2_exists_intervalLocal` (with its `r η` facts), `w5r_box_corners`,
   `w6r_box_centreCorners`; then `w6_branchData … (hCC t ht₂ T₀ hmem) (hL t ht₃ T₀ hmem) hW`.
6. **Body edits (one token each, statements untouched):** `w5b_noninterlacingData` 24711 (`w5b_box_curlData` → `w6k_box_curlData …
   hr0 hr1 hr hη hηr hηr1`, the executor's instruction — it makes `w5b_box_curlData` dead; `w5b_noninterlacingData` itself still
   consumes the turn box and stays dead), `w4_box_returnedRows` 27400 (`w5_box_branch` → `w6_box_branch`), the leaf 27488 (`  sorry` →
   `  exact w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)`, the closure line recorded since W4).

Compiled on the FIRST probe against a prefix olean (`W5[1..24298]` + CURL + … + ROT block, `<scratchpad>/w6glue/pfx/W6AsmPrefix.olean`,
49 s to build; `probes/Probe1.lean` = the glue + the new body of `w4_box_returnedRows` as `w6_test_rows`, 33 s): 0 errors in the glue
(the only error was the leaf-wiring `example`, since `w4_s7_bigon_law_at_of` lies after the prefix cut; the wiring is W4's recorded
sorry-free line and compiles in the full file).  No compile-fix round; the reassessment rule was not triggered.

## 4. Task (3): compile, axioms, frozen statements, clash scan

Compile: header.  **Whole-file `#print axioms`** (scratch `<scratchpad>/w6glue/final/Ax_final.lean` = the file + one `#print axioms`
per named top-level declaration, 1,453 declarations, log `Ax_final.log`, 0 errors): the axiom universe of the file is
`propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness, SM.lit_homfly_descent, SM.ng_finite_word,
SM.src_contact, sorryAx` — **no unregistered axiom anywhere**; `sorryAx` occurs in EXACTLY 19 declarations (§5).

| declaration | axioms |
|---|---|
| **`thm_C_S7`** | **`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]`** |
| `thm_C_S7_of_floor`, `thm_C_S7_of`, **`s7_bigon_law_at`**, `s7_sliding_law_at`, `w4_s7_bigon_law_at_of`, **`w4_box_returnedRows`**, `w6_box_branch`, `w6_branchData`, `w6_noninterlacingData`, `w6k_box_curlData`, `w5_returnedRow_of` | standard + `lit_homfly, lp_lm, lp_lm_uniqueness` |
| `w6_interlacingData`, `w6_interlacingTurnData`, `w6_noninterlacingTurnData`, **`w6r_box_centreCorners`**, `w6r_exists_rotation`, **`w5r_box_corners`**, `w6x_centreCornerData`, `w6c_cornerData`, `w6r_rotation_interlacing`, `w6r_rotation_noninterlacing` | `[propext, Classical.choice, Quot.sound]` |
| the 19 of §5 | `sorryAx` (own or inherited) |

Frozen statements: `python3 tools/stmt_check.py W6_Assembled_B.lean --base W3_Skeleton.lean` → 5/5 byte-identical and unique (PASS);
`tail -n 43` identical to `W3_Skeleton.lean`; the leaf's statement and docstring untouched (only its `  sorry` line replaced).  Clash scan:
header (namespace-aware, against every `.lean` under `work/lean`).  Verbatim check: the assembler `<scratchpad>/w6glue/assemble.py` is
assert-guarded on every boundary (each unit file must equal `W5_Assembled.lean` outside its recorded hunks; CC must equal `W6_COR.lean`
up to `end W5Row` and `W5_Assembled.lean` after the ROT region; the three edited lines must match their W5 text).

## 5. Honest state: `thm_C_S7` is sorry-free; the 19 declarations that still carry `sorryAx` (all dead — on no path to any frozen declaration)

Own `sorry` (8): `s7q_box_ret` 4442 (W3/ROT's S1, false as stated on the leg-`M` side — W3_RET_REPORT §2), `s7z_F_exists` 18058,
`s7z_returned_of_FSector` 18499 (W3/K's B1, B2, superseded by the F-aligned route), `w5b_box_returnedData` 23884 (BR; discharged in the
shape `w5_returnedData`), `w5b_box_interlacingTurnData` 24281, `w5b_box_noninterlacingTurnData` 24290 (BR; per-`t`, no radius —
superseded by `w6_*TurnData`), `w5b_box_curlData` 24664 (BR; superseded by CURL's `w6k_box_curlData`), `w5r_box_branch` 25894 (ROW;
superseded by `w6_box_branch`).  Inherited (11): `s7q_box_rows`, `s7q_exists_contactSector`, `s7q_sliding_law_at_of_boxes`,
`w3_SlidingRet_of_box` (← `s7q_box_ret`); `s7z_exists_rowSector`, `w3_BigonFSector_of_box`, `w3_BigonReturnedRows_of_box` (← K's boxes);
`w5b_interlacingData`, `w5b_noninterlacingData`, `w5_branchData`, `w5_box_branch` (← BR's turn boxes).  **No remaining Prop; no wave 7.**

## 6. Wave 7 — none

Row 110 has no open Prop.  What remains is the port (§7) and the executor's installation steps (copy the three modules into
`work/lean/SM/`, replace `<HH:MM>`, `lake build`, run `tools/check_lean.py` for the fixed names `SM.thm_C_S7`, `SM.thm_comparison`,
`SM.cor_C_inherits`).

## 7. Task (4): the port — `work/drafts/corner/port/CS7_B/` (PORT_REPORT.md there has the full detail)

| module | lines | imports | content | compile (`lean --root -o`, scratch tree) |
|---|---|---|---|---|
| `SM/CS7Units.lean` | 27,000 | `SM.CornerChainUnits SM.CS7Sliding SM.BigonDeletion SM.CarrierFloorRows` | every declaration of `W6_Assembled_B.lean` from `namespace SM` to `end VertexEdge` except the two leaves and the 26 deletions below (468 lines removed), 27 docstring rewordings | 72 s (60 s in the first scratch run; 105 s when a full-file compile ran concurrently) |
| `SM/CS7.lean` | 97 | `SM.CS7Units SM.CarrierFloorRows` | the two leaves (bodies as in the draft), `thm_C_S7_of`, `thm_C_S7_of_floor`, `theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor` — `tools/stmt_check.py port/CS7_B/SM/CS7.lean --base W3_Skeleton.lean` 5/5 PASS | 23 s |
| `SM/ComparisonRows.lean` | 26 | `SM.CS7 SM.CSoft SM.Comparison SM.CInherits` | rows 127/128: `thm_comparison (hR : hyp_R) : … := thm_comparison_of hR thm_C_S7 thm_C_soft`, `cor_C_inherits (hR : hyp_R) : CInheritsData := cor_C_inherits_of hR thm_C_S7 thm_C_soft` (signatures verbatim from `work/drafts/comparison/Comparison_Assembled.lean` 1009-1011, 1016 minus the placeholder's ` by`; the one-liners of `work/drafts/comparison/port/PORT_REPORT.md` §5) | 25 s |

`CS7Units.lean` compiles in 72 s (60 s in the first scratch run; 105 s when a full-file compile ran concurrently) with `-o` (below the ~90 s split threshold), so it was NOT split; the builder
(`port/CS7_B/tools/port_build_B.py --split <line>`) can produce `CS7UnitsA/B` at the unit-F boundary (draft line 8503) if the executor
prefers.  Axioms on the scratch tree (`Axioms.lean`, the `#print axioms` probe lives ONLY there): `thm_C_S7`, `thm_comparison`, `cor_C_inherits` = exactly the nine registered axioms `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]`, no `sorryAx` (probe 23 s).  No `sorry`, `sorried`,
`sorryAx`, `#print`, `#eval`, `#check`, `admit` string in any port file (also not in prose; checked by the builder); four `set_option
linter.unusedSectionVars false in` lines of the units are kept (precedent: nine accepted `SM/*.lean` files carry `set_option`).
Header line 1 of each module: `-- Ported <HH:MM>Z 2026-09-19 from work/drafts/corner/W6_Assembled_B.lean by the pod executor (files
prepared by the W6-GLUE assembler): …` with the literal placeholder `<HH:MM>` (the source is named truthfully as the `_B` file).

**7.1 Deletions (26 declarations, 468 lines incl. attached docstrings / `include … in` lines; every one recorded, none on a proved path):**
the 19 `sorryAx` carriers of §5 and seven sorry-free companions that exist only for them (W4_ASSEMBLY_REPORT §7's list):
`w3_SlidingRet` (the Prop S1, false as stated), `w3_box_rows_of`, `w3_s7_sliding_law_at_of`, `w3_s7_sliding_law_at_of₂` (all take
`hret : w3_SlidingRet`), `w3_BigonFSector`, `w3_BigonReturnedRows` (K's Props B1, B2), `w3_s7_bigon_law_at_of` (takes B1, B2).  The
builder's reference scan finds no code reference to any deleted name in the kept text (prose mentions are reworded, §7.2).
**7.2 Docstring rewordings (27, table `port/CS7_B/tools/reword.json`, each applied exactly once):** every prose `sorry`/`sorried`/`sorryAx`
mention (ROT's module docstring, W3Sliding's S2 remarks, F's "Black boxes (`sorry`, …)", K's `s7z_exists_rowSector` remark and heading E,
the W4Bigon glue docstring incl. "once wave 5 lands" (twice), ROW's "sorried theorem", the W5Glue bullets, BR's Part-6 docstring) and the
`**BLACK BOX …**` heads of the twelve now-proved theorems (`s7q_box_carriers`, `s7f_exists_bigonSplit`, `s7f_exists_twoNewbornTerm`,
`s7f_exists_ineligible_transport`, `s7s_clear_local`, `s7s_wallTriangleData_of_bigon`, `s7z_oneNewborn_exists`, `w5r_box_transport`,
`w5r_box_corners`, `w5r_box_contact`, `w6r_box_centreCorners`, `w4_box_returnedRows`) → `**PROVED (…; formerly BLACK BOX …)**` with the
discharging unit named.  Statements, names and bodies untouched.
**7.3 Collapses: none applied** (not trivial — the duplicates are `def`s used across thousands of lines and the units rely on `exact`-level
unfolding between them).  Kept and listed: `w5r_qH / w5t_qH / w5b_qH`, `w5r_L₁ / w5t_L₁ / w5b_L₁`, `w5r_L₂ / w5t_L₂ / w5b_L₂`, `w5r_x / w5s_x`,
`w5r_T₁ / w5t_T₁ / w5b_ι₁`-preimages, `w5r_sgn_ne_zero / w5_signType_cast_ne_zero`, and W4 §2's content duplicates (`s7g_CarrierData'` vs
S1P's, `s7fa_side_of_r`, `s7fa_sideData`, `s7fa_not_affected_of_ne` vs their B3 twins).

## 8. Deviations and assembler's edits, disclosed

1. **Two assembler instances; `_B` outputs.**  At 12:11-12:13Z this instance wrote its scaffolding (`glue.lean`, `hdr.lean`, `ftr.lean`,
   `lean.sh`, `build_pfx.sh`, `assemble.py`, `header.lean`) into `<scratchpad>/w6asm/` before noticing that another W6-GLUE assembler
   was already using that directory (its `body_rows.lean`, prefix olean and a first `W6_Assembled.lean` at 12:11:48Z).  If that
   instance had files of those names they were overwritten (its conventions — `W6AsmPrefix`, the probe header — were the same); a note
   `w6asm/NOTE_FROM_SECOND_ASSEMBLER.md` records it, this instance moved to `<scratchpad>/w6glue/` and never touched `w6asm/` again, and all
   its outputs carry `_B` (the W5 precedent).  The other instance is not visible from this session (`ListAgents`), so it could not be
   messaged directly.
2. **BR's turn boxes did NOT receive bodies** (the task says to write them): not derivable as stated (§3); restated glue instead, the boxes
   left unproved and UNUSED, dropped at port.  The task's alternative reading ("thread a radius through `w4_box_returnedRows`' intersection")
   is what `w6_box_branch` does.
3. **`w5b_box_curlData` NOT replaced** (CURL's disclosure, W6_CURL_REPORT §2); the executor's one-token re-thread applied inside
   `w5b_noninterlacingData`'s body (statement unchanged) — a body edit of a unit theorem that is itself dead; harmless, recorded.
4. **CC's region taken verbatim from `W6_CC.lean`** (verified: `diff W6_ROT.lean W6_CC.lean` = COR's two hunks + `25590a26035,26819` +
   `25597c26826,26834`), per the executor's note; W6_CC.lean was never edited by this instance.
5. **`w6r_exists_rotation` unused** (§3); kept (sorry-free) as ROT's deliverable in its own shape.
6. Header: W5's eight comment lines replaced by twelve (`1,8c1,12`).  No frozen text, no unit statement/docstring, no import touched.
7. Port header names the source `W6_Assembled_B.lean` (not the task's literal `W6_Assembled.lean`), which is the truth for these files.
8. The reassessment rule (audit after 2 attempts / 60 min) was not triggered anywhere: the glue compiled on its first probe; the port
   builder needed three mechanical fixes (a rewording target present twice → two-line targets; `set_option` present in the units →
   the check relaxed with precedent; the draft's own glue docstring said "sorried" → reworded before assembly).

## 9. Verification record

```
for u in COR ROT CURL CC; do diff W5_Assembled.lean W6_$u.lean | grep '^[0-9<]'; done      # COR 25067a25068,25503 25073c25509,25517; ROT 25096a25097,25627; CURL 24298a24299,24655; CC = COR + 25095a25540,26070(ROT+CC region)
diff W6_ROT.lean W6_CC.lean | grep '^[0-9]'                                                # 25067a25068,25503 25073c25509,25517 25590a26035,26819 25597c26826,26834
for u in COR ROT CURL; do python3 tools/stmt_check.py W6_$u.lean --base W3_Skeleton.lean; tail -n 43 W6_$u.lean | diff -q - <(tail -n 43 W3_Skeleton.lean); python3 tools/clash_scan.py W6_$u.lean; done   # 5/5 PASS, identical, [] / {}
python3 <scratchpad>/w6glue/assemble.py --cc W6_CC.lean --wire --out W6_Assembled_B.lean   # assert-guarded merge
cd work/lean && lake env lean ../drafts/corner/W6_Assembled_B.lean                         # 0 errors; 8 × "declaration uses sorry" (4442 18058 18499 23884 24281 24290 24664 25894); 57 s
cd work/lean && lake env lean <scratchpad>/w6glue/final/Ax_final.lean                      # 1,453 #print axioms; thm_C_S7 = the nine registered axioms; sorryAx in exactly 19
python3 tools/stmt_check.py W6_Assembled_B.lean --base W3_Skeleton.lean                    # 5/5 PASS ; tail -n 43 identical
python3 tools/clash_scan.py W6_Assembled_B.lean                                           # duplicates [] / full_name_clashes {} / 1448 new decls
grep -c sorry W6_Assembled_B.lean                                                          # 20 (8 bodies + 12 prose)
diff W5_Assembled.lean W6_Assembled_B.lean | grep '^[0-9]'                                 # 1,8c1,12 24298a24302,24658 24351c24711 25067a25428,25863 25073c25869,25877 25096a25901,27390 25106c27400 25194c27488
python3 port/CS7_B/tools/port_build_B.py --src W6_Assembled_B.lean --del port/CS7_B/tools/deletions.json --reword port/CS7_B/tools/reword.json --out port/CS7_B
bash port/CS7_B/tools/port_compile_B.sh <scratch> port/CS7_B CS7Units CS7 ComparisonRows   # §7 table; Axioms.lean probe
```
Timeline (UTC): 12:04 start (reports, unit diffs, stmt/clash checks, BR/ROT/CURL/glue interfaces); 12:11 scaffolding (collision, §8.1);
12:16 moved to `w6glue/`, prefix olean 12:17; 12:18 Probe1 clean (glue); 12:19-12:34 port machinery prepared and tested on the pre-CC
draft; 12:36 CC report received; 12:38 assembled, full compile 0 errors; 12:40 axioms/stmt/clash; 12:42 port built; 12:43 (re-timed 12:51) port compiled;
12:52 report.
