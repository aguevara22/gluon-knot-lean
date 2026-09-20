# W3C_ASSEMBLY_REPORT — assembly of row-177 Wave 3c (units SPLITA, SPLITB, SPLITC, KNOT, SITE, BIGON onto `W3B_Assembled.lean`)

Assembler (subagent), 2026-09-15/16, 23:59–00:40 UTC / 7:59–8:40pm ET (hard stop 02:15 UTC not approached).  Inputs:
`W3B_Assembled.lean` (11 851 lines, 7 `sorry` declarations), the six unit files `W3C_{SPLITA,SPLITB,SPLITC,KNOT,SITE,BIGON}.lean`
with their reports, the checkers `check_W3_identity.py`, `check_W3_statements.py`, `clash_scan_W3.py`.  Compile command throughout:
`cd work/lean && lake env lean ../drafts/moves/<file>.lean`.  Nothing under `work/lean` was written; no `lake build`.
Scripts: `assemble_W3C.py` (the mechanical merge; regenerates the file with `python3 assemble_W3C.py` in this directory) and
`assemble_W3C_connect.py` (the assembler's connections, exact unique string replacements + one block removal).

## 0. Result in one paragraph

**`W3C_Assembled.lean` (16 945 lines, 1428 declarations) compiles: exit 0, 0 errors, 34–38 s.**  All six units are in.  The
assembler (i) RESTATED the four false Wave-3 skeleton sub-leaves `w3g_bigonData_smooth_arcST/TS` and
`w3bi_bigonData_smooth_arcST/TS_switch_z` with unit G's non-kink hypothesis and closed them by the units' proved corrected
forms, wiring unit SITE's non-kink box `w3cs_not_kink_site` into `w3bi_bigon_of_site_model` / `w3bi_bigon_of_site` /
`w3bi_bigon_pair_of` (§1.2); (ii) CLOSED SPLITC's black box `w3cc_splitA_corners_data` from SPLITA's carriers (§1.3, 120 lines,
`w3cx_`); (iii) PROVED the sign table (ESC (1c)) for SPLITA's carriers from the alternating triple (`w3cx_sign_table_at`) and reduced
SPLITB's black box `w3cb_split_core_data` and KNOT's black box `w3ck_split_ident_data` to ONE residue `w3cx_outer_residue`
(the parity `#mixedSet = 2Λ` + KNOT's identification clause, §1.4), proving `esc_FullSplitData` at every configuration for
SPLITA's carriers modulo that residue (`w3cx_fullSplitData_at`).  **`sorry` declarations 7 → 4**: the optional
`w3b_reparam_switch`; the frozen OUTER leaf `w3bi_esc_outer_data` (NOT provable as stated — KNOT's rule-3 finding on its two
outer clauses; it is superseded in the operative chain by `w3ck_esc_outer_occ_holds`); SITE's non-kink box
`w3cs_not_kink_site_data`; and the assembler's residue `w3cx_outer_residue_data`.  The five frozen blocks are byte-identical;
40/42 skeleton `w3*_` statements are byte-identical, the 2 others being exactly the deliberately restated `w3g_` sub-leaves; the
row leaf statement is unchanged; 0 name clashes.  **`w3bi_extreme_selected` and `w3ck_extreme_selected : RowShape
@ExtremeSelectedData` are both PROVED as compositions but NOT sorry-free** — the operative (record-clause) chain
`w3ck_extreme_selected` has exactly TWO `sorryAx` sources, `w3cx_outer_residue_data` and `w3cs_not_kink_site_data` (§4).  **The
port is therefore NOT prepared** (criterion of task item (5) not met); §6 gives the honest state for `FINAL_REVIEW`.

| item | result |
|---|---|
| **`work/drafts/moves/W3C_Assembled.lean`** | 16 945 lines, 1428 declarations (base 11 851 + SPLITA 1016 + SPLITC 952 + BIGON 305 + SITE 488 + SPLITB 849 + KNOT 1047 + assembler ≈ 500 (`w3cx_`, 11 declarations) − 63 removed duplicates − moved/replaced bodies) |
| compile | **exit 0, 0 errors**, 34–38 s wall; warnings = the inherited deprecations (`if_pos/if_neg/dif_pos/dif_neg`), unused-variable lints of the units, **4 `declaration uses sorry`** (lines 4093, 11689, 13745, 16425; §3) |
| `sorry` terms | **7 → 4** (§3); `grep -c sorry` = 7 lines (4 terms + 3 prose mentions at 7856, 14706, 16561) |
| `check_W3_identity.py Port_GenericTransportSw_draft.lean W3C_Assembled.lean` | the 5 frozen blocks **IDENTICAL** (`structure G11_ConfigSw` 1206 B, `namespace G11_ConfigSw` block 1252 B, `def G11_core_sw_statement` 1015 B, `theorem G11_core_sw` statement 136 B, `theorem esc_switch_riii_of_chain` 694 B); `imports` line `False` only because of `import RProof.RALedgers` (inherited from Wave 3b; documented W3B §8); `G11_core_sw body starts with sorry: False` |
| `check_W3_statements.py W3C_Assembled.lean` | **40/42** byte-identical; differing = `['w3g_bigonData_smooth_arcST', 'w3g_bigonData_smooth_arcTS']` = exactly the two deliberately restated sub-leaves (§2); `w3a_` 20/20; no skeleton declaration name missing |
| restated (not frozen-row) statements | `w3g_bigonData_smooth_arcST`, `w3g_bigonData_smooth_arcTS` (skeleton sub-leaves), `w3bi_bigonData_smooth_arcST_switch_z`, `w3bi_bigonData_smooth_arcTS_switch_z` (Wave-3b sub-leaves); consumers `w3bi_bigon_of_site_model`, `w3bi_bigon_of_site`, `w3bi_bigon_pair_of` gained the non-kink hypothesis (§1.2) |
| frozen row material | `RowShape @ExtremeSelectedData` (`RALedgers.lean:29`), `Statements_FINAL`/`RALedgers` statements, `w3bi_extreme_selected_leaf`'s statement: untouched (byte-identical to Wave 3b) |
| `#print axioms` (scratch copy, 74 declarations; `W3C_AXIOMS.log`) | §4 — `w3ck_extreme_selected` / `w3bi_extreme_selected`: the registered axioms + `sorryAx`; every unit theorem and every assembler theorem: registered axioms only |
| clash scan (`clash_scan_W3.py work/lean W3C_Assembled.lean`) | 1428 declarations, 1428 distinct fully-qualified names, 0 internal duplicates, **0 fully-qualified clashes**; 925 informational short-name coincidences (the `G11_ParamsSw` copy, unchanged since A1) |
| port (`work/drafts/moves/port/R177/`) | **not prepared** — the row theorem is not sorry-free (§3, §6, §7) |

## 1. Assembly

### 1.1 Mechanical merge (`assemble_W3C.py`)

Each unit file is `W3B_Assembled.lean` with prefixed material inserted and (BIGON, SITE) `sorry` bodies replaced; every unit's
edit was taken as the exact `diff --normal` command list against the base.  **11 edits, pairwise disjoint in base coordinates**
(asserted by the script), applied bottom-up:

| unit | edits (base line → content) |
|---|---|
| SPLITA | insert after 10671 (before the docstring of `w3bi_esc_outer_data`): 1016 lines, `section W3CA_Core` / `section W3CA_Config` (`w3ca_`, 28 declarations) |
| SPLITC | insert after 10675 (after `w3bi_esc_outer_data`): 952 lines, `section W3CC_SplitC` (`w3cc_`, 61 declarations incl. the black box) |
| BIGON | insert after 10768: 230 lines (`w3cz_` transfer + the four switch_z forms + the `iff hk5` theorems); replace 10794 / 10814 (the `sorry` of the two `switch_z` leaves) by the `hk5` reductions; insert after 10890: 68 lines (the two `w3cz_` consumer variants) |
| SITE | insert after 10920: 434 lines (`w3cs_`, D-level + `section W3CS_Lift` + the leaf proof); insert after 10922 / 10923: 54 lines (the body `exact w3cs__w3bi_site_data_data_proof` and the non-kink block `w3cs_NotKink … w3cs_not_kink_site_data`; the base's `sorry` line becomes the non-kink box's body) |
| SPLITB | insert after 11845 (before `end W3BI_REAL`): 849 lines, `section W3CB_SPLITB` (`w3cb_`, 47 declarations) |
| KNOT | insert after 11848 (after `end W3BI_REAL`): 1047 lines, `section W3CK_KNOT` (`w3ck_`, 59 declarations) |

The merged file compiled first time (0 errors, 38 s, 10 `declaration uses sorry` = the base's 7 + SPLITB's + SPLITC's + KNOT's
boxes; SITE had closed β1′ and added the non-kink box).  De-duplication needed: BIGON's `w3cz_bigon_of_site_model_of_not_kink`
/ `w3cz_bigon_of_site_of_not_kink` duplicate what the wired `w3bi_` consumers become — removed (§1.2).  Renames: none (the seven
prefixes `w3ca_ w3cb_ w3cc_ w3ck_ w3cs_ w3cz_ w3cx_` are disjoint; 1428 distinct names).

Dependency order in the file (new material in bold): … `section Row177_6` (G's `w3bg_`, **the restated `w3g_` sub-leaves**, H) →
`section W3BI_REAL` (REAL's (a), the interface Props, **SPLITA `w3ca_`** → `w3bi_esc_outer_data` (open) → **SPLITC `w3cc_` + the
assembler's `w3cx_splitCorners_of_core` / `w3cx_splitA_corners_proof` closing `w3cc_splitA_corners_data`** → **BIGON `w3cz_`** → **the
restated `switch_z` sub-leaves** → `w3bi_SiteData` → **the wired `w3bi_bigon_of_site_model` / `w3bi_bigon_of_site`** → `w3bi_site_data`
→ **SITE `w3cs_`**, `w3bi_site_data_data` (closed), **`w3cs_not_kink_site(_data)`** → **the wired `w3bi_bigon_pair_of/_data`** → β2, `w3ba_`,
`w3bi_hrec_general`, `w3bi_rii_sites_of/_data`, the `w3bi_esc_*` replay, `w3bi_extreme_selected(_leaf)` → **SPLITB `w3cb_`** (its
event-level black-box declarations moved out, §1.4)) → **`section W3CK_KNOT`** (K1–K7, `w3ck_split_ident` → **the assembler's OUTER
residue block `w3cx_splitCore_of_core`, `w3cx_outer_residue(_data)`, `w3cx_fullSplitData_at`, `w3cx_split_ident_of_residue`,
`w3cx_split_core_of_residue`, then `w3cb_split_core_data` (closed modulo the residue), `w3cb_split_geometry_of_core/_data` (moved),
`w3ck_split_ident_data` (closed modulo the residue)** → `w3ck_esc_outer_occ_holds` → K8 the `w3ck_` chain → `w3ck_extreme_selected`).

### 1.2 Task item (2): the four FALSE sub-leaves restated; SITE's non-kink box wired

Rule 3 of units G and BIGON (W3B_G_REPORT §2, W3C_BIGON_REPORT §3): the frozen forms fail only in `BigonData.hk : 5 ≤ k` when the
smoothed crossing is a kink of the one-component lift; BIGON proved the frozen conclusions EQUIVALENT to `hk5` under the frozen
hypotheses.  Per the task these are Wave-3 skeleton sub-leaves, not frozen row statements, so the assembler replaced the
STATEMENTS by the proved corrected forms (the units' `_of_not_kink` theorems verbatim: `clear_vertex` dropped — no corrected form
consumes it — and the non-kink hypothesis `hkink` appended) and the bodies by the corrected theorem applied by name:

| declaration (line) | statement change | body |
|---|---|---|
| `w3g_bigonData_smooth_arcST` (9237) | − `clear_vertex`, + `hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩` | `exact w3bg_bigonData_smooth_arcST_of_not_kink … hkink` |
| `w3g_bigonData_smooth_arcTS` (9267) | − `clear_vertex`, + `hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩` | `exact w3bg_bigonData_smooth_arcTS_of_not_kink … hkink` |
| `w3bi_bigonData_smooth_arcST_switch_z` (13097) | same as `arcST` | `exact w3cz_bigonData_smooth_arcST_switch_z_of_not_kink … hkink` |
| `w3bi_bigonData_smooth_arcTS_switch_z` (13119) | same as `arcTS` | `exact w3cz_bigonData_smooth_arcTS_switch_z_of_not_kink … hkink` |

Docstrings of the four are unchanged (they describe the site); a `-- (W3C assembler) STATEMENT RESTATED …` comment heads each body.
`check_W3_statements.py` reports exactly the two `w3g_` names as differing (the `switch_z` forms are `w3bi_`, outside its 42).

Wiring (bodies = unit BIGON's proved consumer variants, statements = the frozen ones + the non-kink hypotheses):
* `w3bi_bigon_of_site_model` (13163): + `hkST hkTS` (the two conditions); the four calls pass `hkST`/`hkTS` instead of
  `clear_vertex` (which the site data still carries; it is destructured as `-`).
* `w3bi_bigon_of_site` (13206): + `hk : (sS D x).1 = (tS D x).1 → hkST ∧ hkTS` (needed only in the self case; the mixed case uses
  `w3bg_not_kink_of_ne_comp`).
* `w3bi_bigon_pair_of` (13751): + `(hkink : w3cs_not_kink_site)`; `w3bi_bigon_pair_data := w3bi_bigon_pair_of w3bi_site_data_data
  w3cs_not_kink_site_data` (13763).  `w3cs_NotKink D x` is definitionally the conjunction, so `fun _ => kH` serves as `hk`.
* Removed as duplicates (63 lines): BIGON's `w3cz_bigon_of_site_model_of_not_kink`, `w3cz_bigon_of_site_of_not_kink` (a `/-! … -/`
  note marks the place).

Result: `w3g_bigonData_smooth_arcST/TS`, the two `switch_z` forms, `w3bi_bigon_of_site_model`, `w3bi_bigon_of_site`,
`w3bi_bigon_pair_of` are all `[propext, Classical.choice, Quot.sound]`; `w3bi_bigon_pair_data` / `w3bi_rii_sites_data` carry `sorryAx`
ONLY through `w3cs_not_kink_site_data` (β1′ `w3bi_site_data_data` is PROVED by SITE).

### 1.3 Task item (1)/(3): SPLITC's black box closed from SPLITA (`w3cx_`, 120 lines, section `W3CC_SplitC`)

SPLITC stated `w3cc_splitA_corners` (12617) — SPLITA's content in SPLITC's vocabulary `w3cc_SplitCorners` (owners and true corners:
`subset, distinct, memA/B/C, ownZ, ownA/B/C, inherited, cover`).  SPLITA delivered `w3ca_split_config` (`w3ca_CoreData` + the three
fields), `w3ca_sixData_config` (`w3ca_SixData`: twins, `a b c ∉ Q`, adjacencies) and `w3ca_marks_partition_config` (a mark is on
`A ∪ B ∪ C ∪ Z` iff on `q₀'`).  The assembler proved:
* **`w3cx_splitCorners_of_core`** (12650, abstract): `∃ zA zB zC, w3cc_SplitCorners hP Q S q₀ A B C Z zA zB zC` from `D : w3ca_SixData`,
  `hSeq : ∀ x, x ∈ S ↔ x ∈ Q ∨ x = a ∨ x = b ∨ x = c` (instance-free, as `w3ca_core` takes it), `core : w3ca_CoreData`, the three
  definitional equations `A = w3ca_Ac …` etc., and the marks partition.  `zA zB zC` are the `central` clause's inner visits;
  `ownA/B/C` by the orientation case `geoMarkSuccessor hP (inr a₁) = inr b₁` of the definitions (`simp only [w3ca_Ac, …, h,
  ↓reduceIte]`; in the wrong sub-case `Z = owner zX = owner (X's visit) = X` contradicts `distinct`); `inherited` (a `q₀`-corner on
  `Z` would be an inner visit, whose crossing is not in `Q`); `cover` (a true corner of `S` on the four carriers is on `q₀`; its
  crossing is in `Q` or is `a, b, c`, whose two visits are `zX` and `visitTwin zX` by `visit_eq_or_twin`).
* **`w3cx_splitA_corners_proof : w3cc_splitA_corners`** (12743): at the configuration, with the supports transported by
  `GT_outsideSupports_transport` / `GT_fullAvail_transport` and `S' = Q' ∪ T'` read through `P1.mem_triangleCrossings_iff`; the
  definitional equations are `rfl` (`w3ca_A hP S hef heg hfg` unfolds to `w3ca_Ac hP S a₁ a₂ b₁`).
* `w3cc_splitA_corners_data` (12761) `:= w3cx_splitA_corners_proof` — **CLOSED**, `[propext, Classical.choice, Quot.sound]`.  Hence
  SPLITC's `w3cc_fullSplitData_of` is usable at every configuration for SPLITA's carriers (it supplies `distinct`, `central_rot`,
  `outer_alternative`, `uniform`).

### 1.4 Task item (3): the OUTER data modulo ONE residue (`w3cx_`, ≈ 390 lines, section `W3CK_Outer`)

`w3bi_esc_outer_data` could NOT be built: its two outer clauses `w3bi_knot_after_two` / `w3bi_three_components` quantify over every
relational `IsOrientedSmoothing` and are not provable from record-level reasoning (KNOT's rule-3 finding, W3C_KNOT_REPORT §3; KNOT
proved the record-clause forms `w3ck_knot_after_two` / `w3ck_three_components_count` and replayed the whole chain as
`w3ck_extreme_selected`, whose outer input is `w3ck_split_ident` = `esc_FullSplitData` ∧ the identification clause).  What did land is
connected:
* **`w3cx_splitCore_of_core`** (16146): SPLITB's `w3cb_SplitCore` from SPLITA's core data + the sign table ("every triangle visit
  owned by `A`, `B` or `C` has turn `s`") + the parity `#mixedSet = 2Λ`: `localX` = the visit `X` owns (`hitX`) with its turn from the
  table; `neAB/AC/BC` from `distinct`; `central`: a triangle visit not on `A, B, C` is on `Z`, whose marks are the inner visits.
* **The sign table PROVED** (ESC (1c), the clause SPLITB's core needed from SPLITA and neither unit attempted):
  `w3cx_turnAt_selected` (16214; `w3cb_turnAt hP S (inr v) = crossingSign P v.2.val (visitTwin v).2.val` at a selected visit, by
  `geoInEdge_visit` / `geoOutSlot_selected`), **`w3cx_sign_table_of_core`** (16228, abstract: with `A B C Z` SPLITA's carriers by
  definition and `IsAlternating (cs e f) (cs e g) (cs f g)`, `∃ s ≠ 0, ∀ v ∈ T, owner v ∈ {A,B,C} → turnAt v = s` — in the pattern
  `σ a₁ = b₁` the outer visits are `a₁ : e→f`, `b₂ : g→e`, `c₂ : f→g` with turns `cs(e,f)`, `−cs(e,g)`, `cs(f,g)`, all `= cs(e,f)` by
  alternation, `Z` owning `a₂, b₁, c₁` (`central`); in the mirror pattern `a₂, b₁, c₁` with turns `= cs(e,g)`; `s ≠ 0` by
  `CV.crossingSign_visit_twin_ne_zero`), **`w3cx_sign_table_at`** (16356, at the configuration: `w3e_alt_of_completeLocal` at `t`
  transported to `t'` by `AV_EventRadius.sign_eq`, exactly as unit SITE did).  All `[propext, Classical.choice, Quot.sound]`.
* **`def w3cx_outer_residue`** (16399) — the ONE residue, binders of `w3ck_split_ident`: `∃ Λ, [#w3cb_mixedSet Q' (Q' ∪ T') q₀' = 2Λ] ∧
  w3ck_three_components_ident_occ (carrierDiagram_L q₀') … Λ (groupedPoly w3ca_A) (groupedPoly w3ca_B) (groupedPoly w3ca_C)`;
  **`w3cx_outer_residue_data`** (16425) the one new `sorry`.
* **`w3cx_fullSplitData_at`** (16433): `esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' (w3ca_A …) (w3ca_B …) (w3ca_C …)
  (w3ca_Z …) Λ` given the residue's sign table and parity — SPLITA's `touching_iff`, `central_no_piece` (`w3ca_split_at_outer`),
  the corner ledger (§1.3), SPLITB's `writhe`, `mixed` (`w3cb_fields_of_residue` on the core with `w3cb_triangle_on_contact_at`),
  assembled by SPLITC's `w3cc_fullSplitData_of`.  Standard axioms only.
* **`w3cx_split_ident_of_residue : w3cx_outer_residue → w3ck_split_ident`** (16482), **`w3cx_split_core_of_residue : w3cx_outer_residue →
  w3cb_split_core`** (16492) — both take the sign table from `w3cx_sign_table_at`; `w3cb_split_core_data` (16507) and
  `w3ck_split_ident_data` (16525) are now theorems on the residue
  (statements unchanged).  SPLITB's three event-level declarations `w3cb_split_core_data`, `w3cb_split_geometry_of_core`,
  `w3cb_split_geometry_data` were MOVED from `section W3CB_SPLITB` (a note at 15502) to after the residue (they need KNOT's
  `w3ck_three_components_ident_occ`, declared later); statements and the two proofs are verbatim.

Compile after each connection step: 0 errors (35–37 s).  The assembler's material (`w3cx_`, 11 declarations) is
`[propext, Classical.choice, Quot.sound]` except the two `_of_residue` theorems (`+ lit_homfly` through the Props' statements).

## 2. Statement identity

`check_W3_identity.py`: 5/5 IDENTICAL.  `check_W3_statements.py`: 40/42; the two differing names are exactly the restated
`w3g_bigonData_smooth_arcST` / `w3g_bigonData_smooth_arcTS` (§1.2; the change is `− clear_vertex, + hkink`, body = corrected form).
Also restated (Wave-3b, not in the 42): `w3bi_bigonData_smooth_arcST_switch_z`, `w3bi_bigonData_smooth_arcTS_switch_z`; consumers
with added hypotheses: `w3bi_bigon_of_site_model`, `w3bi_bigon_of_site`, `w3bi_bigon_pair_of`.  NOT changed: `RowShape
@ExtremeSelectedData`, `w3bi_extreme_selected(_leaf)`'s statements (byte-identical to Wave 3b, which verified them against
`RALedgers.lean:2330` and the fixed `RProof.extreme_selected`), every `Statements_FINAL` / `RALedgers` statement, the frozen `w3bi_`
Props (incl. `w3bi_knot_after_two`, `w3bi_three_components`, `w3bi_esc_outer` — left as KNOT left them, rule 3, with the corrected
`w3ck_` forms next to them), all unit statements.  Imports: unchanged from Wave 3b (`RProof.RALedgers` added there).

## 3. Every remaining `sorry` (4 terms in 4 declarations; line = the `sorry` term − 1 = the declaration)

| decl line | declaration | owner | status / what closes it | est. size |
|---|---|---|---|---|
| 4093 | `w3b_reparam_switch` | (b) | optional helper, NO consumer, not in any row chain | ≈ 0.15k |
| 11689 | `w3bi_esc_outer_data : w3bi_esc_outer` | frozen OUTER leaf (Wave 3b) | **NOT provable as stated** (KNOT rule 3: `w3bi_knot_after_two` / `w3bi_three_components` quantify over every relational `IsOrientedSmoothing`; the library identifies the record only of `smoothDiagram`).  Its `esc_FullSplitData` conjunct IS proved modulo the residue (`w3cx_fullSplitData_at`).  Superseded in the operative chain by `w3ck_esc_outer_occ_holds` (16537).  Port-time: statement edit of the two Props + the `rii_after_smoothing_weak` field (KNOT §3), or adopt the `w3ck_` chain | statement edit |
| 13745 | `w3cs_not_kink_site_data : w3cs_not_kink_site` | SITE (new box) | the non-kink condition at `x_H`, `x_L` under the binders of `w3bi_site_data`: NOT implied by `w3bi_SiteData` (SITE §4 gives a kink loop satisfying D4, D5, `clear`, `clear_vertex`); needs data from the 177 configuration (the carrier edges `G11_mE`, `G11_pE` of `x_ef` not at cyclic distance 2 in `geoCornerPolygon`; routes in SITE §4 (i)/(ii)).  Consumed by `w3bi_bigon_pair_data` → `w3bi_rii_sites_data` → both row chains | ≈ 0.3–0.6k if a route exists; may need an event-level hypothesis |
| 16425 | `w3cx_outer_residue_data : w3cx_outer_residue` | assembler (residue of SPLITB/KNOT) | two clauses at a common `Λ`: **(i) the parity** `#w3cb_mixedSet Q' (Q'∪T') q₀' = 2Λ` (KNOT's bridge count, analogue of `r176m_bridge_count`: the mixed crossings of `J_L` are the retained crossings of `q₀'` between distinct outer carriers, all positive; `Λ` is then fixed by (17)); **(ii) KNOT's identification** `twoLambda J_L = 2Λ ∧ ∃ σ : Fin 3 ≃ Fin J_L.Γ.c, homfly (knotRestrict (σ i)) = groupedPoly A/B/C` in record-clause form (route and API in KNOT §5, §8: `r176s_smoothRestrictIso` pattern twice, `Stack.restrictSmoothIso`, a restrict-of-restrict lemma not in the library, `CV.crossKeep_liftBlock_iff`, `r176s_homfly_of_liftBlock`).  The sign table (1c) that SPLITB's core also needed is PROVED (`w3cx_sign_table_at`).  Consumed by `w3ck_split_ident_data` and `w3cb_split_core_data` | (i) ≈ 0.3–0.5k, (ii) ≈ 0.4–0.8k: **≈ 0.7–1.3k** |

Prose mentions of the word (no term): 7856 (unit G's header), 14706 (SPLITB's header), 16561 (KNOT's chain docstring) — to reword at
port time.  Closed in this wave: `w3bi_site_data_data` (SITE), `w3g_bigonData_smooth_arcST/TS` and the two `switch_z` forms (restated,
G/BIGON), `w3cc_splitA_corners_data` (assembler from SPLITA), the sign table (assembler, `w3cx_sign_table_at`), `w3cb_split_core_data` and
`w3ck_split_ident_data` (assembler, modulo the residue).  Chains: `w3ck_extreme_selected := w3ck_esc_ledger w3ck_esc_interface_ext_occ_holds CV.carrierSlotFloor`;
`w3ck_esc_interface_ext_occ_holds := w3ck_esc_interface_ext_of w3ck_esc_outer_occ_holds w3bi_rii_sites_data`;
`w3ck_esc_outer_occ_holds := w3ck_esc_outer_occ_of w3ck_split_ident_data`; `w3ck_split_ident_data := w3cx_split_ident_of_residue
w3cx_outer_residue_data`; `w3bi_rii_sites_data := w3bi_rii_sites_of w3bi_bigon_pair_data w3bi_wall_data_data`; `w3bi_bigon_pair_data :=
w3bi_bigon_pair_of w3bi_site_data_data w3cs_not_kink_site_data`.  So the `sorryAx` sources of **`w3ck_extreme_selected` are exactly
`w3cx_outer_residue_data` and `w3cs_not_kink_site_data`**; `w3bi_extreme_selected` (the Wave-3b chain) has in addition
`w3bi_esc_outer_data`.

## 4. `#print axioms` (scratch copy `W3C_Axioms_scratch.lean` = the file + 74 `#print axioms` lines before `end SM.Link`, compiled from this directory and deleted; exit 0, 0 errors; output `W3C_AXIOMS.log` next to this report)

| declaration | axioms |
|---|---|
| **`w3ck_extreme_selected`**, `w3bi_extreme_selected`, `w3bi_extreme_selected_leaf` | `propext, sorryAx, Classical.choice, Quot.sound, lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact` (the registered set of `esc_ledger` + `CV.carrierSlotFloor`, plus `sorryAx` from §3) |
| **`w3ck_esc_ledger`, `w3ck_esc_interface_ext_of`, `w3ck_rii_after_smoothing_weak_occ`, `w3bi_esc_ledger`, `w3bi_esc_interface_ext_of`, `w3bi_switch_riii`, `w3bi_rii_after_smoothing_weak`, `G11_core_sw`, `esc_switch_riii_of_chain`, `w3e_strong_case_sw`** | `propext, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness` — **no `sorryAx`** |
| `w3ck_esc_outer_occ_of`, `w3cx_split_ident_of_residue`, `w3cx_split_core_of_residue` | standard + `lit_homfly` (through the Props' statements) — no `sorryAx` |
| `w3ck_esc_outer_occ_holds`, `w3ck_split_ident_data`, `w3cb_split_core_data`, `w3cb_split_geometry_data`, `w3cx_outer_residue_data`, `w3bi_esc_outer_data` | standard + `lit_homfly` + `sorryAx` |
| `w3bi_esc_interface_ext_holds` | the six registered + `sorryAx` (via `w3bi_esc_outer_data`, `w3bi_rii_sites_data`) |
| `w3bi_rii_sites_data`, `w3bi_bigon_pair_data`, `w3cs_not_kink_site_data`, `w3b_reparam_switch` | `propext, sorryAx, Classical.choice, Quot.sound` |
| **all of the following: `[propext, Classical.choice, Quot.sound]`** — the restated `w3g_bigonData_smooth_arcST/TS`, `w3bi_bigonData_smooth_arcST/TS_switch_z`, the wired `w3bi_bigon_of_site_model`, `w3bi_bigon_of_site`, `w3bi_bigon_pair_of`, `w3bi_rii_sites_of`; SITE's `w3bi_site_data_data`, `w3cs__w3bi_site_data_data_proof`, `w3cs_site_data_lift`, `w3cs_siteData_of_triangle`; G/BIGON's `w3bg_…_of_not_kink` ×2, `w3cz_…_switch_z_of_not_kink` ×2, `w3cz_bigonData_switch_transfer`; the assembler's `w3cc_splitA_corners_data`, `w3cx_splitA_corners_proof`, `w3cx_splitCorners_of_core`, `w3cx_splitCore_of_core`, `w3cx_turnAt_selected`, `w3cx_sign_table_of_core`, `w3cx_sign_table_at`, `w3cx_fullSplitData_at`; SPLITB's `w3cb_split_geometry_of_core`, `w3cb_fields_of_residue`, `w3cb_fullSplitData_of_residue`, `w3cb_triangle_on_contact_at`, `w3cb_markChildren_of`, `w3cb_central_no_piece`; SPLITA's `w3ca_split_at_outer`, `w3ca_central_rot_at_outer`, `w3ca_split_config`, `w3ca_marks_partition_config`, `w3ca_core`, `w3ca_pattern`; SPLITC's `w3cc_fullSplitData_of`, `w3cc_outer_alternative_of`, `w3cc_uniform_of`, `w3cc_central_rot_of`, `w3cc_rot_ledger`; KNOT's `w3ck_knot_after_two`, `w3ck_three_components_count`, `w3ck_interlaces_iff_arcs`, `w3ck_isSelfCrossing_smooth_iff`; `w3bi_wall_data_data`, `w3bi_hrec_general` | |

No unregistered axiom anywhere.  The criterion of task item (5) ("exactly the registered axioms, no `sorryAx`") is NOT met for either
row theorem; `RProof.extreme_selected` was therefore not declared and no port files were written.

## 5. Name-clash scan

`clash_scan_W3.py work/lean W3C_Assembled.lean`: 1428 declarations, 1428 distinct fully-qualified names, 0 internal duplicates,
**0 fully-qualified clashes** with `work/lean/**/*.lean` (`.lake` excluded, `RProof/RALedgers.lean` included); 925 informational
short-name coincidences, all the inherited `G11_ParamsSw` ↔ `RProof.G11_Params` ones.  Copies of library material under unit prefixes
(no clash, to be dropped at port time by importing): `w3bh_restrictCrossings_iso_of_recordIso` (= `SM.CB.…`), `w3cb_insert_eq`
(= `CV.cvt165s_insert_eq`), `w3cc_uniformOrOneDissent_of_pattern` / `w3cc_rot_ray` (= `CV.SingletonDi`'s), `w3cc_principalAngle_swap`
(= `SM.ZeroRotationSeed`'s), `w3cs_exact_symm` (= `s174_exact_symm`), KNOT's K2 (= the draft `R176_SMOOTH` §R1, not a module).

## 6. Honest state for `FINAL_REVIEW` (row 177, `R:extreme_selected`, fixed name `RProof.extreme_selected`) — the port is not prepared

**Row 177: ledger, switched-RIII core, (4) realiser, site data (β1′), wall data (β2), record lemma, the corrected bigon sites,
the sign table, `esc_FullSplitData` for SPLITA's carriers (modulo the residue), the two outer counts (record-clause form) PROVED on
registered axioms; 2 named leaves open in the operative chain.**  Precisely (all in `work/drafts/moves/W3C_Assembled.lean`, 0 errors, 34–38 s):

* **PROVED, registered axioms only, no `sorryAx`**: everything Wave 3b had (`G11_core_sw`, `w3e_strong_case_sw`,
  `esc_switch_riii_of_chain`, `w3bi_switch_riii`, `w3bi_rii_after_smoothing_weak`, the F-177-2 replay and ledger `w3bi_esc_*`,
  `w3bi_wall_data_data`, `w3bi_hrec_general`, `w3bi_rii_sites_of`, units E/H/G's corrected forms), plus this wave: β1′ the site
  data `w3bi_site_data_data` (SITE: D4 as a determinant identity, D5 from the positive over-strand convention, the lift wiring);
  the four bigon sites in their corrected (non-kink) statements and their consumers; SPLITA's `touching_iff`, `distinct`,
  `central_no_piece`, `central_rot` with the explicit carriers `w3ca_A/B/C/Z` and the marks partition; SPLITC's
  `outer_alternative`, `uniform`, `central_rot` from the corner ledger, which the assembler derived from SPLITA
  (`w3cc_splitA_corners_data` CLOSED); SPLITB's `writhe`, `mixed` from its core, the children clauses from three iterated
  insertions, `central_no_piece`; the assembler's sign table (1c) for SPLITA's carriers (`w3cx_sign_table_at`); KNOT's `w3ck_knot_after_two` (`D_H^{xy}` a knot) and `w3ck_three_components_count`
  (`D_L^{xy}` has three components) at every configuration, the record ↔ `GeometricInterlaces` bridge, and the corrected
  chain `w3ck_esc_interface_ext_of` / `w3ck_esc_ledger`.
* **PROVED modulo the residue** (`w3cx_outer_residue_data`): `esc_FullSplitData` at every configuration
  (`w3cx_fullSplitData_at`), `w3cb_split_core_data`, `w3ck_split_ident_data`, `w3ck_esc_outer_occ_holds`.
* **Rule-3 findings recorded**: (a) `w3g_bigonData_smooth_arcST/TS` and the two `switch_z` forms were false as stated (kink) —
  RESTATED here with the non-kink hypothesis (§1.2); (b) `w3bi_knot_after_two` / `w3bi_three_components` (hence the frozen
  `w3bi_esc_outer` and its leaf `w3bi_esc_outer_data`) are not provable as stated — NOT edited; the record-clause forms
  `w3ck_knot_after_two_occ` / `w3ck_three_components_occ` and the `w3ck_` chain are the operative ones (port-time statement edit of
  the Wave-3b skeleton: the two Props and the `rii_after_smoothing_weak` field of `w3bi_esc_MoveDataWeak`; `RALedgers` unaffected).
* **OPEN — the `sorryAx` sources of `w3ck_extreme_selected`, exactly two:**
  | leaf | est. size | note |
  |---|---|---|
  | `w3cx_outer_residue_data` | **≈ 0.7–1.3k** | parity `#mixedSet = 2Λ` ≈ 0.3–0.5k + KNOT's identification (`twoLambda J_L = 2Λ`, the three knot restrictions ↔ `groupedPoly A/B/C`) ≈ 0.4–0.8k; §3 |
  | `w3cs_not_kink_site_data` | ≈ 0.3–0.6k, route open | the lift crossing over `x_ef` is not a kink of the one-component lift; not a consequence of the site data (SITE §4); may need a hypothesis on the event |
  Plus, outside the operative chain: the frozen `w3bi_esc_outer_data` (statement edit, not mathematics) and the optional
  `w3b_reparam_switch` (≈ 0.15k).  **Total to close row 177: ≈ 1.0–1.9k lines** + the two skeleton statement edits.
* Not changed: `RProof/RALedgers.lean`, `Statements_FINAL.lean`, the five frozen blocks, the row leaf statement, every frozen
  `w3bi_` Prop.

Suggested `FINAL_REVIEW.md` §4.4 row text: `| 177 | R:extreme_selected | RProof.extreme_selected | pending | ledger + switched-RIII
core + (4) realiser + site data + corrected bigon sites + sign table + esc_FullSplitData (mod. residue) + both outer counts PROVED
on registered axioms (work/drafts/moves/W3C_Assembled.lean, 0 errors); 2 leaves open in the operative w3ck_ chain: the OUTER
residue (parity + identification, ≈ 0.7–1.3k) and the non-kink condition at the site (≈ 0.3–0.6k, route open); 4 skeleton
sub-leaf statements restated (non-kink hypothesis), 2 more to restate at port time (record clauses) — W3C_ASSEMBLY_REPORT.md §6 |`.

## 7. What the port would look like (when the two leaves close)

Per task item (5): `RProof/GenericTransportSw.lean` = lines 1–7846 of this file (the trans-free copy over `G11_ConfigSw` + the
`W3Switch`/`W3E` skeleton material; ≈ 20 s of the 35 s, so no BC/DE split needed for time); `RProof/ExtremeSelectedUnits.lean` =
`section Row177_6` + `section W3BI_REAL` + `section W3CK_KNOT` (units E/G/H/REAL/`w3ba_`/SPLITA/SPLITC/BIGON/SITE/SPLITB/KNOT/`w3cx_`);
`RProof/ExtremeSelected.lean` = `theorem extreme_selected : RowShape @ExtremeSelectedData := w3ck_extreme_selected` in `namespace
RProof`.  Before porting: (a) the two skeleton statement edits of §6 (rule 3 (b)); (b) reword the three prose mentions of the word
`sorry` (7856, 14706, 16561) and the `-- (W3C assembler)` comments that name it; (c) drop the library copies of §5 by importing
`SM.CBProducts`, `CV.SingletonDi`, `SM.ZeroRotationSeed` (or keep them); (d) decide whether the frozen `w3bi_` chain
(`w3bi_esc_outer_data`, `w3bi_extreme_selected`) is deleted or kept as documentation of the Wave-3b interface.

## 8. Pitfalls / notes

* The six units' hunks against the base were disjoint, so the merge is exact; `assemble_W3C.py` asserts it and `assemble_W3C_connect.py`
  asserts each connection string is unique (a change of any unit file fails loudly).  The SITE hunks look odd (`10922a` + `10923a`):
  `diff` re-used the base's `  sorry` line as the body of the new non-kink box; the merged result is right (compile: β1′ closed).
* `refine { f₁ := …, f₂ := … }` for a `Prop` structure with a continuation line indented less than the first field fails
  ("unexpected identifier; expected '}'") — the anonymous constructor `⟨…⟩` in field order avoids the layout rule.
* A `/-! … -/` module comment directly after a `/-- … -/` docstring is a parse error ("expected 'lemma'"); when replacing a
  theorem, include its docstring in the replaced text.
* `geomAt E t ht.1` vs `(genericAt E t ht.1).crossingGeometry`: defeq, and `exact`/application unify them (SPLITA pitfall 4), so
  SPLITA's `GeoComponent (geomAt …)` carriers go straight into `esc_FullSplitData hn (genericAt …) …`, `w3cc_fullSplitData_of`
  and `w3cb_fields_of_residue`; `rw` would not see them.
* `(visitOn x v h).1` is `x` by `rfl`, so `Or.inl rfl` proves `(visitOn (xPair hef) e _).1 = xPair hef ∨ …` and `visit_eq_or_twin a₁ w h`
  accepts `h : w.1 = xPair hef`.
* `#print axioms` lines go before the final `end SM.Link` (after the anonymous `end`); the scratch copy was compiled from
  `work/drafts/moves/` and deleted afterwards.
* `SignType` is not a `SubtractionMonoid`: `neg_ne_zero` does not apply; `(by decide : ∀ a : SignType, a ≠ 0 → -a ≠ 0)` does.
  `IsAlternating sa sb sc` is `sa = sc ∧ sb = -sa` and does NOT imply `sa ≠ 0`; the nonzero sign comes from
  `CV.crossingSign_visit_twin_ne_zero`.
* Times (UTC / ET): 23:59 / 7:59pm start (reading the six reports); 00:02 first merged compile (0 errors, 10 sorry-declarations);
  00:07 task-(2) connections compiled (0 errors, 6); 00:12 SPLITC box closed from SPLITA (first try, 5); 00:18 OUTER residue
  block (2 layout/parse errors) → 00:20 compiled (0 errors, 4); 00:21 axioms scratch copy, checks; 00:26 first report;
  00:28–00:33 the sign table proved (`w3cx_turnAt_selected`, `w3cx_sign_table_of_core`, `w3cx_sign_table_at`; one error, a
  `SignType` negation lemma, fixed by `decide`) and the residue shrunk to parity + identification (0 errors, 4); 00:34 axioms
  (74 prints, 0 errors), checks; 00:40 this report.
