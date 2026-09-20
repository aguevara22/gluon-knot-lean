# W3B_ASSEMBLY_REPORT — assembly of row-177 Wave 3b (units E, G, H, REAL onto `W3_A1_Assembled.lean`)

Assembler (subagent), 2026-09-15 23:01–23:20 UTC / 7:01–7:20pm ET (bounded window, hard stop 2026-09-16 01:00 UTC
not approached).  Inputs: `W3_A1_Assembled.lean` (7827 lines, 10 `sorry`), `W3B_E.lean` + `W3B_E_REPORT.md`,
`W3B_G.lean` + `W3B_G_REPORT.md`, `W3B_H.lean` + `W3B_H_REPORT.md`, `W3B_REAL.lean` + `W3B_REAL_REPORT.md`, the
three checkers `check_W3_identity.py`, `check_W3_statements.py`, `clash_scan_W3.py`.  Compile command throughout:
`cd work/lean && lake env lean ../drafts/moves/<file>.lean` (toolchain of `work/lean`).  Nothing under `work/lean`
was written; no `lake build`.

## 0. Result in one paragraph

**`W3B_Assembled.lean` (11 851 lines, 1193 declarations) compiles: exit 0, 0 errors, 35 s.**  Every closed sub-leaf
of the four units is in (unit E: 3/3, unit H: 4/4, unit REAL: the (4) realiser, the (6) realiser in the weak form, the
wall data β2, the F-177-2 interface replay and the ledger); the assembler additionally closed REAL's black box
`w3bi_hrec_general` (its three non-`ST/ST` orientation cases) by connecting it to unit H (§1.2).  The five frozen
blocks and all 42 frozen `w3*_` statements are byte-identical; the leaf statement `w3bi_extreme_selected_leaf` is
byte-identical (after the name) to the fixed `RProof.extreme_selected` statement; 0 name clashes against `work/lean`.
**`w3bi_extreme_selected : RowShape @ExtremeSelectedData` is PROVED as a composition but NOT sorry-free**: `sorryAx`
enters through exactly six named leaves (§3), all on the (6) site / outer-data side; nothing on the (4) side or in the
ledger carries `sorryAx`.  **The port is therefore NOT prepared** (criterion of task item (5) not met); §6 gives the
honest state for `FINAL_REVIEW`.

| item | result |
|---|---|
| **`work/drafts/moves/W3B_Assembled.lean`** | 11 851 lines, 1193 declarations; = base 7828 + E 184 + G 1375 + H 1101 + REAL 1180 + assembler 188 (§1) |
| compile | **exit 0, 0 errors**, 35 s wall; 70 warnings = 51 `if_pos/if_neg/dif_pos/dif_neg/push_neg` deprecations (inherited, cosmetic) + 12 unused-variable lints (units G/H, kept deliberately per their reports) + **7 `declaration uses sorry`** (§3) |
| `sorry` terms | base **10 → 7** (E closed 3, H closed 4, G reduced 2 to `hk5`, REAL added 7 of which the assembler closed 3, REAL's 4 boxes remain) — exact list §3 |
| `check_W3_identity.py Port_GenericTransportSw_draft.lean W3B_Assembled.lean` | the 5 frozen blocks **IDENTICAL** (`structure G11_ConfigSw` 1206 B, `namespace G11_ConfigSw` block 1252 B, `def G11_core_sw_statement` 1015 B, `theorem G11_core_sw` statement 136 B, `theorem esc_switch_riii_of_chain` 694 B incl. body); the `imports` line prints `False` ONLY because of the added `import RProof.RALedgers` (REAL's; needed for `esc_switch_riii`, `esc_FullSplitData`, the `esc_` helpers and the ledger) — the imports are the draft's + `SM.BigonDeletion` + `RProof.RALedgers`, nothing else |
| `check_W3_statements.py W3B_Assembled.lean` | **42/42** `w3[a-h]_` statements byte-identical to the skeleton (`theorem … := by`), 20/20 `w3a_`, no skeleton declaration name missing |
| leaf statement | `w3bi_extreme_selected_leaf` after the name, to `:=`, is byte-identical to `theorem extreme_selected` in `work/drafts/cvtail/Wave1_Assembled.lean:4197`, `PREREVIEW_probes.lean:803` and `U_SLOT.lean:874`; `w3bi_extreme_selected : RowShape @ExtremeSelectedData` is `RProof.esc_ledger`'s conclusion (`RALedgers.lean:2330`) verbatim; the row's fixed name is `RProof.extreme_selected` (`axiom-policy.json` targets) |
| `#print axioms` (scratch `W3B_Axioms.lean`, 51 declarations) | §4 — `G11_core_sw`, `w3e_strong_case_sw`, `esc_switch_riii_of_chain`, `w3bi_switch_riii`, `w3bi_rii_after_smoothing_weak`, `w3bi_esc_interface_ext_of`, `w3bi_esc_contact_identity`, `w3bi_esc_couple`, `w3bi_esc_ledger`: **registered axioms only, no `sorryAx`**; `w3bi_extreme_selected`: `sorryAx` via `w3bi_esc_interface_ext_holds` only |
| clash scan (`clash_scan_W3.py work/lean W3B_Assembled.lean`) | 1193 declarations, 1193 distinct fully-qualified names, 0 internal duplicates, **0 fully-qualified clashes**; 925 informational short-name coincidences (the `G11_ParamsSw` copy mirrors `RProof.G11_Params` name for name — unchanged from the A1 scan) |
| port (`work/drafts/moves/port/R177/`) | **not prepared** — `w3bi_extreme_selected` is not sorry-free (§3, §6) |
| scripts | `assemble_W3B.py` (regenerates the file: `python3 assemble_W3B.py` in this directory) + `assemble_W3B_connect.py` (the assembler's connections, derived from `W3B_H.lean`'s text) |

## 1. Assembly (how the five files were joined)

### 1.1 Mechanical merge (`assemble_W3B.py`)

Each unit file is `W3_A1_Assembled.lean` with `sorry` bodies replaced and prefixed material inserted, so each unit's
edit was taken as the exact `diff --normal` command list against the base (no fuzzy context): **13 edits, only
`  sorry` lines removed (10 in total: E 3, G 2, H 4 — REAL removes none), pairwise disjoint in base coordinates**
(asserted by the script), applied bottom-up:

| unit | edits (base line → content) |
|---|---|
| REAL | insert after 6: `import RProof.RALedgers`; insert after 7822 (after `end Row177_6`): `section W3BI_REAL … end W3BI_REAL`, 1179 lines |
| E | replace 7552 / 7570 / 7603 (`sorry` of `w3e_xs_point`, `w3e_liftVisit_σD_sw`, `w3e_recordIsoData_sw`) by 63 / 58 / 66 lines (bodies + the two `w3be_` helpers, which E placed inside the same hunks) |
| G | insert after 7665 (after `open Smoothing` in `section Row177_6`): the `w3bg_` block, 1370 lines; replace 7699 / 7726 (`sorry` of `w3g_bigonData_smooth_arcST/TS`) by the reduction `exact w3bg_…_of_five … (by sorry)` (4 / 3 lines) |
| H | insert after 7727 (after the `w3g_` declarations): the `w3bh_` helpers and cores, 849 lines; replace 7757 / 7770 / 7779 / 7820 (`sorry` of `w3h_record_core`, `w3h_smooth_record_occ`, `w3h_restrict_switch_deleted`, `w3h_hrec`) by 79 / 9 / 99 / 64 lines (bodies + the bridge `w3bh_reduced_to_smooth`) |

De-duplication: none needed — the four units' new declaration sets are disjoint by prefix (`w3be_` 2, `w3bg_` 26,
`w3bh_` 27, `w3bi_` 39) and no unit re-declares another's name (the merged file has 1193 distinct fully-qualified
names, 0 internal duplicates).  Renames: none.  The first compile of the merged file (before the connections) was
already 0 errors (36 s, 8 `declaration uses sorry`).

Dependency order in the file (unchanged where inherited): frozen `G11_ConfigSw` → `G11_ParamsSw` copy (BC + DE) →
`section W3Switch` → connectors → `G11_core_sw` → `section W3E` (unit E's three sub-leaves + `w3be_` helpers →
`w3e_strong_case_sw`) → `esc_switch_riii_of_chain` → `section Row177_6` (G's `w3bg_` block → the two `w3g_`
sub-leaves → H's `w3bh_` helpers → `w3h_record_core`, `w3h_smooth_record_occ`, `w3h_restrict_switch_deleted`,
`w3bh_reduced_to_smooth`, `w3h_hrec`) → `section W3BI_REAL` (REAL's (a), the interface Props, β1/β1′, β2 with the
nested `section W3BI_Lift`, **the assembler's `w3ba_` block**, `w3bi_hrec_general`, `w3bi_rii_sites_of`, (b),
`w3bi_esc_interface_ext_of/holds`, the replayed `w3bi_esc_contact_identity` / `w3bi_esc_couple` / `w3bi_esc_ledger`,
`w3bi_extreme_selected`, `w3bi_extreme_selected_leaf`).

### 1.2 Connections (`assemble_W3B_connect.py`; the only assembler-authored Lean material, 188 lines, prefix `w3ba_`)

REAL's `w3bi_hrec_general` (line 11 427; the `w3ba_` block at 11 245–11 425) is `w3h_hrec` with the disjunction `(B.y = y₀ ∧ B.z = z₀) ∨ (B.y = z₀ ∧
B.z = y₀)` on each side; REAL proved the `ST/ST` case from `w3h_hrec` by name and left the three other orientation
pairs `sorry`, noting that `reducedRecord` is symmetric in `B.y, B.z`.  Checked against unit H's proof: `BigonData.keep
= {c | c ≠ crossingOf (overVisit B.y) ∧ c ≠ crossingOf (overVisit B.z)}` (BigonDeletion:101) and `hBy, hBz` enter
`w3bh_reduced_to_smooth` in exactly one `rw` (Step A/B, the identification of `B.keep` with the occurrence set `X₁`);
`w3h_hrec` uses `hB*y, hB*z` only to call that bridge.  So the connector derives, from the text of `W3B_H.lean`:
* `w3ba_reduced_to_smooth_gen` — `w3bh_reduced_to_smooth` with hypothesis `hB : (B.y = y₀ ∧ B.z = z₀) ∨ (B.y = z₀ ∧
  B.z = y₀)`; body identical except the one step, which becomes `rcases hB … · rw [hBy, hBz]; exact (hX₁ u).symm ·
  rw [hBy, hBz]; exact and_comm.trans (hX₁ u).symm`;
* `w3ba_hrec_gen` — `w3h_hrec` with `hBH`, `hBL` disjunctions, calling `w3ba_reduced_to_smooth_gen` (four token
  changes);
* the three `· sorry` of `w3bi_hrec_general` → `exact w3ba_hrec_gen … B_H (Or.inl/inr ⟨hBHy, hBHz⟩) B_L (Or.inl/inr
  ⟨hBLy, hBLz⟩)`; the docstring's last sentence reworded accordingly.
Both `w3ba_` lemmas and `w3bi_hrec_general` are `[propext, Classical.choice, Quot.sound]` (§4); the unit-H originals are
untouched.  Compile after the connection: 0 errors, 35 s, 7 `declaration uses sorry`.

Not connectable (shapes do not match; nothing invented): `w3bi_bigonData_smooth_arcST_switch_z` / `_TS_switch_z` are
REAL's corrected forms with the switch at `z₀`, while unit G proved only the switch-at-`y₀` forms (`w3bg_…_of_five`,
`_of_not_kink`); `w3bi_site_data_data` and `w3bi_esc_outer_data` have no counterpart in any unit.  The two frozen
`w3g_` sub-leaves stay as unit G left them (false as stated, reduced to `hk5`, §3).

## 2. Statement identity (details in the table of §0)

`check_W3_identity.py`: 5/5 IDENTICAL; `check_W3_statements.py`: 42/42, 0 differing/missing, no missing skeleton
names; the frozen `w3g_` statements are byte-identical although their bodies are now reductions (unit G changed only the
body).  `imports`: `SM.Smoothing SM.MarkedProducts SM.SingleCrossing CV.FullTwist RProof.GenericTransport
SM.BigonDeletion RProof.RALedgers` (draft's 5 + `SM.BigonDeletion` + REAL's `RProof.RALedgers`); the A1 clash scan
already covered `RALedgers.lean`, and this file's scan covers all of `work/lean`.  `w3bi_extreme_selected_leaf`'s
statement: byte-identical to the fixed `extreme_selected` (three cvtail sources agree); `RowShape` is
`RALedgers.lean:29`.

## 3. Every remaining `sorry` (7 terms in 7 declarations; line = the `sorry` term, decl = the `theorem` line)

| line | decl | declaration | unit | status / what closes it |
|---|---|---|---|---|
| 4095 | 4093 | `w3b_reparam_switch` | (b) | optional, no consumer (≈ 0.15k); NOT in the `w3bi_extreme_selected` chain |
| 9257 | 9237 | `w3g_bigonData_smooth_arcST` | G | **FALSE as stated** (rule 3, `W3B_G_REPORT.md` §2: `BigonData.hk : 5 ≤ k` fails when the smoothed crossing is a kink of the one-component lift); body = `exact w3bg_bigonData_smooth_arcST_of_five … (by sorry)`, the `sorry` being exactly `hk5 : 5 ≤ (Γ₀.comp (M.strandOf cutStartS _).1).k`.  PROVED corrected forms: `w3bg_…_of_five`, `w3bg_…_of_not_kink` (hypothesis `⟨s.1, s.2−1⟩ ≠ ⟨t.1, t.2+1⟩`) |
| 9286 | 9267 | `w3g_bigonData_smooth_arcTS` | G | same, `hk5` on the component of `cutStartT`; corrected forms `w3bg_bigonData_smooth_arcTS_of_five` / `_of_not_kink` PROVED |
| 10674 | 10673 | `w3bi_esc_outer_data : w3bi_esc_outer` | — (outside Wave 3b's units) | the OUTER interface data: `esc_FullSplitData` (ESC §1, §4–§5) + `knot_after_two` + `three_components` at a common `Λ`, at every configuration of the extended interface |
| 10794 | 10777 | `w3bi_bigonData_smooth_arcST_switch_z` | G (corrected form, REAL §4β) | the `w3g_` statement with the bigon read on `(D^x).switch z₀` (needed when `f` is over `e` at `x_ef`); statement only.  Carries the same `hk` defect as the `w3g_` forms (identical hypotheses) |
| 10814 | 10797 | `w3bi_bigonData_smooth_arcTS_switch_z` | G (corrected form) | same |
| 10923 | 10922 | `w3bi_site_data_data : w3bi_site_data` | G-site + D4/D5 (β1′) | `w3bi_SiteData` on both lifts (`g, y, z, hy/hz, clear, clear_vertex, hover`, the coherent orientation, `y ≠ x ≠ z`); decomposition into 5 sub-obligations in `W3B_REAL_REPORT.md` §8 |

(The word `sorry` also occurs once in a comment, line 7856 of the `w3bg_` header.)  Chain into the row theorem:
`w3bi_extreme_selected := w3bi_esc_ledger w3bi_esc_interface_ext_holds CV.carrierSlotFloor`;
`w3bi_esc_interface_ext_holds := w3bi_esc_interface_ext_of w3bi_esc_outer_data w3bi_rii_sites_data`;
`w3bi_rii_sites_data := w3bi_rii_sites_of w3bi_bigon_pair_data w3bi_wall_data_data`;
`w3bi_bigon_pair_data := w3bi_bigon_pair_of w3bi_site_data_data`, and `w3bi_bigon_pair_of` consumes
`w3g_bigonData_smooth_arcST/TS` and the two `switch_z` forms by name (in `w3bi_bigon_of_site_model`).  So the
`sorryAx` sources of `w3bi_extreme_selected` are exactly the six declarations of rows 2–7 above.

## 4. `#print axioms` (scratch copy `W3B_Axioms.lean` in the assembler's scratchpad = the file + 51 `#print axioms` lines placed inside `namespace SM.Link`; exit 0, 0 errors; the printed output is kept as `W3B_AXIOMS.log` next to this report)

| declaration | axioms |
|---|---|
| **`SM.Link.G11_core_sw`** (Wave-3 leaf), **`esc_switch_riii_of_chain`** (177 (4) of the chain), **`w3e_strong_case_sw`** (the switched `G11_strong_case`) | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — **no `sorryAx`** |
| **`w3bi_switch_riii`** ((4) realiser: `esc_switch_riii` on the carrier diagrams) | the same six — **no `sorryAx`** (unit E closed the three `w3e_` boxes it depended on) |
| **`w3bi_rii_after_smoothing_weak`** ((6) realiser, weak form, given `w3bi_rii_sites`), **`w3bi_esc_interface_ext_of`**, **`w3bi_esc_contact_identity`**, **`w3bi_esc_couple`**, **`w3bi_esc_ledger`** (the F-177-2 replay and the ledger) | the same six — **no `sorryAx`** |
| **`w3bi_extreme_selected`**, `w3bi_extreme_selected_leaf` | `propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact` — the extra registered axioms enter through `CV.carrierSlotFloor` (row 155 / SM row 99) as in `esc_ledger`; `sorryAx` enters ONLY through `w3bi_esc_interface_ext_holds` |
| `w3bi_esc_interface_ext_holds` | the six + `sorryAx` (via `w3bi_esc_outer_data`, `w3bi_rii_sites_data`) |
| `w3bi_rii_sites_data`, `w3bi_bigon_pair_data`, `w3bi_bigon_pair_of`, `w3bi_bigon_of_site_model` | `propext, sorryAx, Classical.choice, Quot.sound` (via `w3bi_site_data_data`, `w3g_*`, the `switch_z` forms) |
| `w3bi_esc_outer_data` | `propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly` (own `sorry`; `lit_homfly` through the Prop's statement) |
| `w3bi_site_data_data`, `w3bi_bigonData_smooth_arcST_switch_z`, `_TS_switch_z`, `w3g_bigonData_smooth_arcST`, `_TS`, `w3b_reparam_switch` | `propext, sorryAx, Classical.choice, Quot.sound` (own `sorry`) |
| **`w3bi_rii_sites_of`**, **`w3bi_hrec_general`**, `w3ba_hrec_gen`, `w3ba_reduced_to_smooth_gen` (assembler), `w3bi_wall_data_data`, `w3bi_wallEquiv`, `w3bi_adjacent_lift_proof`, `w3bi_alt_swap` | `[propext, Classical.choice, Quot.sound]` (`w3bi_rii_sites_of` and `w3bi_hrec_general` carried `sorryAx` in `W3B_REAL.lean`; closed by §1.2) |
| `w3h_hrec`, `w3h_record_core`, `w3h_smooth_record_occ`, `w3h_restrict_switch_deleted`, `w3bh_reduced_to_smooth`, `w3bh_core_pure₀`, `w3bh_core_comp_pure` (unit H) | `[propext, Classical.choice, Quot.sound]` |
| `w3e_xs_point`, `w3e_liftVisit_σD_sw`, `w3e_recordIsoData_sw`, `w3be_lift_six`, `w3be_liftVisit_fst_eq_iff` (unit E) | `[propext, Classical.choice, Quot.sound]` |
| `w3bg_bigonData_smooth_arcST_of_five`, `_TS_of_five`, `_ST_of_not_kink`, `_TS_of_not_kink`, `w3bg_hk5_arcST_of_not_kink`, `_TS_`, `w3bg_line_convexHull` (unit G) | `[propext, Classical.choice, Quot.sound]` |
| `G11_ParamsSw.w3c_homfly_M₁sw` | standard + `SM.lit_homfly` (unchanged) |

Registered axioms: `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` (`SM/LinkInterfaces.lean`) and, through
`CV.carrierSlotFloor`, `SM.lit_homfly_descent`, `SM.ng_finite_word`, `SM.src_contact` — the same footprint
`RProof.esc_ledger` has with `CV.carrierSlotFloor` (`W3B_REAL_REPORT.md` §0).  No unregistered axiom anywhere.

## 5. Name-clash scan

`clash_scan_W3.py work/lean W3B_Assembled.lean` (namespace-aware, tracks `namespace`/`end`): 1193 declarations, 1193
distinct fully-qualified names, 0 internal duplicates, **0 fully-qualified clashes** with any declaration in
`work/lean/**/*.lean` (excluding `.lake`; `RProof/RALedgers.lean` included).  925 informational short-name
coincidences, all the A1 scan's (`SM.Link.G11_ParamsSw.<gu*>` ↔ `RProof.G11_Params.<gu*>` etc.); the new prefixes
`w3be_ w3bg_ w3bh_ w3bi_ w3ba_` coincide with nothing.  Unit H's `w3bh_restrictCrossings_iso_of_recordIso` is a copy of
`SM.CB.restrictCrossings_iso_of_recordIso` (CBProducts:1358, not in the import closure) under a different name — no
clash; at port time either import `SM.CBProducts` and drop the copy, or keep it.

## 6. Honest state for `FINAL_REVIEW` (row 177, `R:extreme_selected`, fixed name `RProof.extreme_selected`) — the port is not prepared

**Row 177: ledger proved, switched RIII core proved, (4) realised, (6) realised modulo the site data; 6 named leaves
open.**  Precisely (all in `work/drafts/moves/W3B_Assembled.lean`, 0 errors, 35 s):

* **PROVED on registered axioms only** (`propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm,
  SM.lp_lm_uniqueness`): the switched G11 core `G11_core_sw` (trans-free copy of the accepted G11 assembly over
  `G11_ConfigSw`, 6.4k lines) and `w3e_strong_case_sw`; the chain form `esc_switch_riii_of_chain`; the (4) realiser
  `w3bi_switch_riii` (`esc_MoveData.switch_riii` on the carrier diagrams, both relabelling cases, D3 by genericity);
  the (6) realiser `w3bi_rii_after_smoothing_weak` given the site box; the F-177-2 interface replay
  `w3bi_esc_interface_ext_of`, `w3bi_esc_contact_identity`, `w3bi_esc_couple` and the ledger `w3bi_esc_ledger :
  w3bi_esc_interface_ext → CV.CarrierSlotFloor → RowShape @ExtremeSelectedData`; the wall data β2
  (`w3bi_wall_data_data`), the record lemma in the general orientation form (`w3bi_hrec_general`, all four cases),
  the site glue `w3bi_rii_sites_of`, and units E and H in full.
* **PROVED but with a false frozen statement** (rule 3): the `j = 2` bigon sites `w3g_bigonData_smooth_arcST/TS` fail
  only in `BigonData.hk : 5 ≤ k` when the smoothed crossing is a kink; `w3bg_…_of_five` / `_of_not_kink` are the
  corrected, sorry-free forms.  Fix = add the non-kink hypothesis to the frozen statement at port time (and derive it
  in the site data) — a statement edit of the Wave-3b skeleton, not new mathematics.
* **OPEN — 6 named leaves, all on the (6) site / outer side, `sorryAx` sources of `w3bi_extreme_selected`:**
  | leaf | est. size | note |
  |---|---|---|
  | `w3bi_esc_outer_data : w3bi_esc_outer` | **≈ 3.3–5.6k** | `esc_FullSplitData` (≈ 3–5k, "U-SPLIT's geometry three times over", `cvtail/U_R177_REPORT.md` item 4) + `knot_after_two` / `three_components` (≈ 0.3–0.6k, item 3); not a Wave-3b unit — the largest open item |
  | `w3bi_site_data_data : w3bi_site_data` (β1′) | ≈ 0.6–1k | D4/D5 site data on both lifts; decomposition `W3B_REAL_REPORT.md` §8 (D4, the coherent orientation from the sign table, is the riskiest 0.2–0.4k) |
  | `w3g_bigonData_smooth_arcST`, `w3g_bigonData_smooth_arcTS` | ≈ 0.1–0.2k (inside β1′) + a statement edit | false as stated; reduced to `hk5`; corrected forms PROVED |
  | `w3bi_bigonData_smooth_arcST_switch_z`, `_TS_switch_z` | ≈ 0.3–1k | the switch-at-`z₀` forms (needed when `f` is over `e` at `x_ef`); same `hk` defect; content = unit G's `_of_five` proofs with the roles of `y₀, z₀` in `same_over` swapped (copy ≈ 0.5k each, or ≈ 0.15–0.3k via a `BigonData` transfer across the two switched diagrams, whose shadows agree and of whose fields only `same_over` sees the over data) |
  Optional, not in the chain: `w3b_reparam_switch` (≈ 0.15k).  **Total to close row 177: ≈ 4.5–8k lines**, dominated
  by the outer data.
* Not changed: `RProof/RALedgers.lean` (the F-177-2 replay lives in the draft as `w3bi_esc_*`, D2 / D-RM-5); no frozen
  statement, name or docstring of the skeleton.

Suggested `FINAL_REVIEW.md` §4.4 row text: `| 177 | R:extreme_selected | RProof.extreme_selected | pending | ledger +
switched-RIII core + (4) realiser PROVED on registered axioms (work/drafts/moves/W3B_Assembled.lean, 0 errors); (6)
realised modulo the site data; 6 named leaves open (outer data ≈ 3.3–5.6k, site data ≈ 0.6–1k, bigon forms ≈ 0.4–1.2k)
— W3B_ASSEMBLY_REPORT.md §6 |`.

## 7. What a port would look like (when the six leaves close)

Per task item (5): `RProof/GenericTransportSw.lean` = the copy + skeleton material (lines 1–7846 of this file minus the
`W3E`/`Row177_6` sections' `sorry`-free content stays; the per-file check is 35 s for all 11.8k lines, so a BC/DE split
is not needed for time), `RProof/ExtremeSelectedUnits.lean` = `section Row177_6` + `section W3BI_REAL` (units E/G/H/REAL
+ `w3ba_`), `RProof/ExtremeSelected.lean` = `theorem extreme_selected : RowShape @ExtremeSelectedData :=
w3bi_extreme_selected` in `namespace RProof` (fixed name).  Prose to reword before porting (no `sorry`/`#print`/`#eval`
strings): the `w3bg_` header comment (line 7856), the unit docstrings that name `sorry`, and this file's `W3BI_REAL`
header.  The `w3g_` statement fix (non-kink hypothesis) must be applied in the skeleton first.

## 8. Pitfalls / notes

* The units' hunks against the base are disjoint, so the merge is exact; `assemble_W3B.py` asserts it — if a future
  unit file touches an overlapping range the script fails loudly rather than guessing.
* `#print axioms` lines must sit inside `namespace SM.Link` (before the closing `end` / `end SM.Link`); the file also
  closes an anonymous section at its end.  `w3c_homfly_M₁sw` is `G11_ParamsSw.w3c_homfly_M₁sw`.
* The identity checker's `imports` line is a strict equality with the draft's imports + `SM.BigonDeletion`; it will
  print `False` for any file that imports `RProof.RALedgers`, which REAL's material requires.  Everything else it checks
  is IDENTICAL.
* Times (UTC / ET): 23:01 / 7:01pm start; 23:04 first merged compile (0 errors, 8 sorry-warnings); 23:07 connection
  written; 23:10 connected compile (0 errors, 7); 23:12 axioms + checks; 23:20 this report.
