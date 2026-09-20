# PORT REPORT — row 177 (R:extreme_selected), port-ready modules

Row-177 wave-3d assembler, 2026-09-19 08:05 UTC / 4:05am ET.  Source: `work/drafts/moves/W3D_Assembled.lean` (21 748 lines,
1 667 declarations, sha256 `04d99e497b75c5a7…`; compiles with 0 errors and 0 `declaration uses` warnings,
`W3D_ASSEMBLY_REPORT.md`).  Nothing written under `work/lean`; `lake build` never run.  Output: three modules under
`work/drafts/moves/port/R177/`, laid out as they land (generator `../../port_R177.py`, re-runnable):

| module (port path → work/lean path) | Assembled lines | lines | md5 | compile (module semantics, §2) | `sorry` / `#print` / `#eval` |
|---|---|---|---|---|---|
| `port/R177/RProof/GenericTransportSw.lean` → `RProof/GenericTransportSw.lean` (the G11 core on a SWITCHED positive diagram: the trans-free copy `G11_ConfigSw` / `G11_ParamsSw`, W3Switch `w3b_`, D8′/E′ `w3c_`/`w3d_`/`w3de_`, `w3e_strong_case_sw`, `esc_switch_riii_of_chain`; no row theorem) | 1–7, 12–7835 verbatim (+ 10 new header lines, + `end` / `end SM.Link`) | 7 845 | `48c20b3a10e888e6d73d12295ffb4488` | 0 errors, 24 deprecation warnings (inherited: `if_pos`/`if_neg`/`dif_pos`/`dif_neg`), 47 s with `-o`/`-i`; olean 14 MB | 0 / 0 / 0 |
| `port/R177/RProof/ExtremeSelectedUnits.lean` → `RProof/ExtremeSelectedUnits.lean` (row 177 (6) and the realisers: units E/G/H, REAL, SPLITA, SPLITC, BIGON, SITE, SPLITB, NONKINK, KNOT, RESPAR, RESID, the assembler's `w3cx_`, the terminal `w3ck_extreme_selected : RowShape @ExtremeSelectedData`; no row theorem) | 7837–21748 verbatim (+ 11 new header lines, 5 imports, a new module docstring, the opening `namespace SM.Link / open SM / noncomputable section`) | 13 944 | `044adb975705c505175942defde89f6e` | 0 errors, 47 warnings (27 inherited deprecations, 12 unused-variable notes, 7 `unusedSectionVars` notes, 1 naming-convention note on the pre-existing `w3cs__w3bi_site_data_data_proof`), 51 s with `-o`/`-i`; olean 26 MB | 0 / 0 / 0 |
| `port/R177/RProof/ExtremeSelected.lean` → `RProof/ExtremeSelected.lean` (row 177) | — (new: the row block, §1.3) | 48 | `19a38268571df9d7f7488bd426a88a39` | 0 errors, 0 warnings, 24 s (import-bound) | 0 / 0 / 0 |

Import graph: `SM.Smoothing`, `SM.MarkedProducts`, `SM.SingleCrossing`, `CV.FullTwist`, `RProof.GenericTransport`,
`SM.BigonDeletion`, `RProof.RALedgers` (the Wave-3 skeleton's import block, verbatim) ← `RProof.GenericTransportSw`;
`RProof.GenericTransportSw`, `RProof.ExtremeTransportUnits` (accepted row-176 units, for `r176s_`/`r176c_`/`r176l_`/`r176o_`),
`SM.CBProducts`, `CV.SingletonDi`, `SM.ZeroRotationSeed` (the three library modules whose copies were dropped, §3) ←
`RProof.ExtremeSelectedUnits` ← `RProof.ExtremeSelected`.  No cycle: nothing in `work/lean` imports any of the three new
modules (`grep -rn 'import RProof.GenericTransportSw\|import RProof.ExtremeSelected'` empty), every imported module is
already built (`.lake/build/lib/lean/{SM,CV,RProof}`), and `work/lean/RProof/` has none of the three files.  All three are
matched by the lakefile glob `RProof.+`.  Probe (NOT for landing; it carries `#print axioms` / `#check`):
`…/scratchpad/w3d/R177Probe.lean`, output `probe_port.log` next to this report.

## 1. Contents

### 1.1 `RProof/GenericTransportSw.lean` — the switched G11 core (assembled lines 1–7, 12–7835)
Header (10 `--` lines, new; `<HH:MM>Z` placeholder for the landing time), the seven imports, the skeleton's module docstring
(`/-! # The G11 core on a switched positive diagram (row 177 (4)) — Wave 3 skeleton (unit U-W3-0) …`, verbatim), then
`namespace SM.Link / open SM / noncomputable section` and `section RIIISw … end RIIISw` + `esc_switch_riii_of_chain`, closed
by the new `end` / `end SM.Link`.  1 091 declarations: `G11_ConfigSw` (structure + 38 namespace declarations, 6 top-level),
`G11_ParamsSw` (the trans-free copies of the accepted `RProof.G11_Params` Units B–D/D8/E: `gu3_` 111, `gu4_` 221, `gu5_`
127 + `gu5_Side` 10, `gu6_` 392, 91 others such as `X₀`, `X₁`, `M₀`, `M₁`, `D₀sw`, `M₀sw`, `M₁sw`), `w3a_` 20, `w3b_` 13,
`w3bc_` 4, `w3be_` 2, `w3c_` 4, `w3d_` 1, `w3de_` 34, `w3e_` 11, `esc_switch_riii_of_chain`.  The five FROZEN blocks
(`G11_ConfigSw`, its namespace block, `G11_core_sw_statement`, the statement of `G11_core_sw`, `esc_switch_riii_of_chain`)
are byte-identical to `Port_GenericTransportSw_draft.lean` (`check_W3_identity.py` on this file: all five IDENTICAL).
The optional, never-consumed `w3b_reparam_switch` (the skeleton's one remaining `sorry` in this range) is DELETED
(W3D_ASSEMBLY_REPORT.md §2).

### 1.2 `RProof/ExtremeSelectedUnits.lean` — everything else except the row theorem (assembled lines 7837–21748)
Header (11 `--` lines, new; `<HH:MM>Z` placeholder), the five imports, a new module docstring, the frame
`namespace SM.Link / open SM / noncomputable section`, then the assembled file from its `/-! ## 5. Row 177 (6)` header to
its end, verbatim (incl. the closing `end` / `end SM.Link`).  576 declarations, all in `SM.Link`, all prefixed:

| block (sections) | prefix | decls | content |
|---|---|---|---|
| Row177_6: unit G (`w3g_` / `w3bg_`), unit H (`w3h_` / `w3bh_`), `w3ba_` | `w3g_` 2, `w3bg_` 26, `w3h_` 4, `w3bh_` 26, `w3ba_` 2 | 60 | the corrected `j = 2` bigon sites `w3g_bigonData_smooth_arcST/TS` (restated with the non-kink hypothesis, §A-18 item 1), the reduced-smoothed-record lemma `w3h_hrec`, `w3h_smooth_record_occ`, `w3ba_hrec_gen` |
| W3BI_REAL: unit REAL | `w3bi_` | 19 | `w3bi_switch_riii` (row 177 (4)), the site data β1′ `w3bi_site_data` / `w3bi_site_data_data`, the wall data β2 `w3bi_wall_data` / `w3bi_wall_data_data`, `w3bi_hrec_general`, `w3bi_bigon_of_site` (+ model), the restated `w3bi_bigonData_smooth_arcST/TS_switch_z` |
| W3BI_REAL: SPLITA / SPLITC / BIGON / SITE / SPLITB | `w3ca_` 28, `w3cc_` 57, `w3cz_` 11, `w3cs_` 15, `w3cb_` 46 | 157 | the carrier split of `Q ∪ T` on the empty side (`w3ca_A/B/C/Z`, `w3ca_split_config`), the corner ledger and rotation lane (`w3cc_`), the switch-at-`z₀` bigon forms (`w3cz_`), the site data lift and `w3cs_NotKink` (`w3cs_`), the writhe / mixed fields and `w3cb_mixedSet` (`w3cb_`) |
| W3BI_REAL: unit NONKINK (steps 1–7) | `w3dk_` | 102 | a reparametrisation of an all-positive diagram induces a `RecordIso`; the oriented smoothing is natural in `RecordIso`; the flat subdivision `w3dk_subdivReparam`; the value form of the site data `w3dk_rii_value_sites` / `w3dk_rii_value_sites_data` (kink case included) |
| W3CK_KNOT: unit KNOT + the assembler's `w3cx_` | `w3ck_` 55, `w3cx_` 11 | 66 | the record-clause outer clauses `w3ck_knot_after_two_occ` / `w3ck_three_components_occ`, `w3ck_esc_outer_occ`, the sign table `w3cx_sign_table_at`, `w3cx_fullSplitData_at`, the residue Prop `w3cx_outer_residue` and its PROVED leaf `w3cx_outer_residue_data` |
| W3CK_Outer: unit RESPAR | `w3dp_` | 70 | the parity clause `w3dp_parity_at` / `w3dp_parity_at_proof`, the bridge `w3dp_twoLambda_eq_card_mixedSet` (`2Λ(J_L) = #mixedSet`), the record-level components of a double smoothing |
| W3CK_Outer: unit RESID | `w3di_` | 97 | the identification clause `w3di_ident_at`, the restrict-of-restrict lemmas, the word on the contact carrier, `w3di_outer_residue_proof`; `w3di_parity_data := w3dp_parity_at_proof` |
| W3CK_Chain: the ledger replay and the chain | `w3ck_` 2, `w3dk_` 2 | 4 (of the counts above) | `w3dk_rii_after_smoothing_weak_occ`, `w3dk_esc_interface_ext_of`, `w3ck_esc_interface_ext_occ_holds`, `w3ck_esc_contact_identity` / `w3ck_esc_couple` / `w3ck_esc_ledger`, **`w3ck_extreme_selected : RowShape @ExtremeSelectedData`** |

No interface Prop is asserted with an open body; every `_data` theorem is proved (§2).

### 1.3 `RProof/ExtremeSelected.lean` — the row theorem
```lean
import RProof.ExtremeSelectedUnits

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-- **Row 177 (ORDER 174), R:extreme_selected** … (the printed obligation quoted verbatim from RProof/X1Rows.lean 1742–1753) … -/
theorem extreme_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ :=
  SM.Link.w3ck_extreme_selected n hn E e f g h3 h4e h4f h4g hE

end RProof
```
The seven statement lines are byte-identical to `work/drafts/cvtail/Statements_FINAL.lean` lines 803–809 (without the
trailing ` by`) — the FIXED statement of the row theorem that RALedgers' port omitted — and to the accepted sibling
`RProof/ExtremeTransport.lean` lines 39–45 after substituting `extreme_transport ↦ extreme_selected`,
`ExtremeTransportData ↦ ExtremeSelectedData` (both equalities are asserted by `port_R177.py`).  Frame identical to
`ExtremeTransport.lean` / `GenericSelected.lean` / RALedgers 22/24/45.  `RowShape @ExtremeSelectedData` (RALedgers.lean 29)
is this statement with `n` explicit; `#check @RProof.extreme_selected` (probe_port.log) prints exactly the `RowShape` body.

## 2. Compile recipe used (true module semantics without touching `work/lean`)

Scratch tree `T/RProof/{GenericTransportSw,ExtremeSelectedUnits,ExtremeSelected,R177Probe}.lean`; `O/RProof/` = symlinks to
every file of `work/lean/.lake/build/lib/lean/RProof/` (55 files); then from `work/lean`, in this order (`port_chain.log`):
1. `lake env sh -c 'LEAN_PATH="O:$LEAN_PATH" lean --root=T -o O/RProof/GenericTransportSw.olean -i O/RProof/GenericTransportSw.ilean T/RProof/GenericTransportSw.lean'` — exit 0, 0 errors, 24 deprecation warnings, 47 s; olean 14 MB.
2. `… -o O/RProof/ExtremeSelectedUnits.olean -i … T/RProof/ExtremeSelectedUnits.lean` — exit 0, 0 errors, 47 linter/deprecation warnings, 51 s; olean 26 MB.
3. `… -o O/RProof/ExtremeSelected.olean -i … T/RProof/ExtremeSelected.lean` — exit 0, no output, 24 s.
4. `… lean --root=T T/RProof/R177Probe.lean` (`import RProof.ExtremeSelected` + `#print axioms` / `#check`) — exit 0, 22 s:

```
'RProof.extreme_selected' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent,
  SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]
'SM.Link.w3ck_extreme_selected' depends on axioms: (the same nine)
'SM.Link.w3cx_outer_residue_data' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
'SM.Link.w3dp_parity_at_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.Link.w3di_ident_at' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
'SM.Link.w3dk_rii_value_sites_data' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
'SM.Link.G11_core_sw' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
```
Exactly `axiom-policy.json`'s `standard` (3) + `literature` (6); **no `sorryAx`**.  The same list was obtained from a scratch
copy of the assembled single file (`../../W3D_AXIOMS.log`, 31 declarations).  The three literature axioms beyond the ledger's
reads (`lit_homfly_descent`, `ng_finite_word`, `src_contact`) enter only through `CV.carrierSlotFloor`, as for rows 174/176.
After the executor copies the three files to `work/lean/RProof/`, the ordinary `lake build` suffices (glob `RProof.+`); lake
orders them by the imports (`GenericTransportSw` → `ExtremeSelectedUnits` → `ExtremeSelected`).

## 3. Deviations from verbatim (complete list)

* `GenericTransportSw.lean` lines 1–10: new header comment.  Lines 11–17 = assembled 1–7 (the seven imports); lines 18–7841
  = assembled 12–7835 byte-for-byte (the assembled file's four extra imports at lines 8–11 belong to the Units module; the
  one trailing blank line 7836 of the range dropped); lines 7842–7845 = the new `⏎ end ⏎ end SM.Link` closing the skeleton's
  `noncomputable section` / `namespace SM.Link`.
* `ExtremeSelectedUnits.lean` lines 1–11: new header comment; 12–16: the import block (`RProof.GenericTransportSw` new, the
  other four are the assembled file's lines 8–11); 18–25: new module docstring; 27/29/31: the frame `namespace SM.Link`,
  `open SM`, `noncomputable section` (the assembled file's lines 38/40/42); lines 33–13944 = assembled 7837–21748 byte-for-byte
  (`port_R177.py` asserts the equality).
* `ExtremeSelected.lean` lines 1–7: new header comment; line 8: `import RProof.ExtremeSelectedUnits`; the module docstring,
  frame, row docstring and theorem are new (the statement lines are the fixed text, §1.3).
* Nothing else.  No declaration statement or proof differs from `W3D_Assembled.lean`.  Strings `sorry`, `#print`, `#eval`:
  0 in each of the three `.lean` files and in the two logs (`grep -rcE`); this report is the only file under `port/R177/` that
  contains the three words, as the names of the strings checked.

## 4. Clash scan

Namespace-aware (`clash_scan_W3.py ../../lean <file>`, every `work/lean/**/*.lean` outside `.lake`): `GenericTransportSw`
1 091 declarations, `ExtremeSelectedUnits` 576, `ExtremeSelected` 1 — **0 fully-qualified clashes** each, 0 internal
duplicates; the informational short-name coincidences are the inherited `SM.Link.G11_ParamsSw.gu*_` ↔ `RProof.G11_Params.gu*_`
ones (the trans-free copies).  `RProof.extreme_selected` is declared nowhere in `work/lean` (RALedgers deliberately omitted the
row theorem; X1Rows.lean mentions the name only in comments).  `work/lean/RProof/` has none of the three module files.

## 5. Executor items

1. Copy the three files of `port/R177/RProof/` to `work/lean/RProof/`; fill the `<HH:MM>Z` placeholder in line 1 of each;
   `lake build`.  Do NOT copy the probe (it is not in `port/R177/`).
2. `lean-declarations.json`: the `R:extreme_selected` entry → `declaration: RProof.extreme_selected`, `module:
   RProof.ExtremeSelected`, plus the statement review per the rows' protocol (the statement is the Statements_FINAL / X1Rows
   text, so the reviewer input is the seven lines of §1.3 with the body withheld).
3. Register / AUTHOR_NOTES / FINAL_REVIEW (W3D_ASSEMBLY_REPORT.md §6): §A-15 closes (row 177 proved on the registered nine);
   §A-16 closes (the residue's two clauses, RESPAR + RESID); §A-17 closes as "not a consequence of the configuration data;
   not needed — the leaf `w3cs_not_kink_site_data` was FALSE as stated and is deleted; the (6) content is realised in the
   value form `w3dk_rii_value_sites_data`; no event-level hypothesis added, FR-R-177-K does not arise"; §A-18 items 1–3
   recorded (the four restated bigon sub-leaves; the Wave-3b Props and leaf deleted; the two prose mentions reworded).
4. Then rows 178 (`RProof.cv_R`, §A-19: the staged one-liner `cv_R_of_rows generic_selected extreme_pair_zero
   extreme_transport extreme_selected`) and 183 (`Bridge.sm_R`), then 184.
5. Optional later refactors (not part of this port): replace `w3bh_reduced_to_smooth` / `w3h_hrec` by NONKINK's bigon-free
   `w3dk_reduced_to_smooth_free` / `w3dk_hrec_free` (~150 lines of duplication, W3D_NONKINK_REPORT.md §4.4); move the
   library-grade material (NONKINK steps 1–4 → a `SM/FlatSubdivision.lean`, RESID's R0–R4 restriction lemmas, RESPAR's
   record-level component lemmas) to shared homes; drop `w3cs_exact_symm` by importing `RProof.GenericSelectedUnits`
   (`s174_exact_symm`); prune the now-unconsumed helpers of the deleted Wave-3b chain, if any remain.
