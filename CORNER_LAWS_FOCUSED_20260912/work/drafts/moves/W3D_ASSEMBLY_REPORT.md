# W3D_ASSEMBLY_REPORT — assembly of row-177 Wave 3d (units RESPAR, RESID, NONKINK onto `W3C_Assembled.lean`): the row is CLOSED and the port is prepared

Assembler (subagent), 2026-09-19, 07:33–08:10 UTC / 3:33–4:10am ET, under D-AUTH-20260919 (no time bound; the author's
response was already recorded verbatim in `work/AUTHOR_NOTES.md` L6520 and `work/AUTHOR_RESPONSE_20260919.md` — verified
identical to `/workspace/repos/lean/author_response.md`, nothing there touched).  Inputs: `W3C_Assembled.lean` (16 945 lines,
1 427 declarations by the regex used here, sha256 `dbcd10375ac572c0…`), the three unit files `W3D_{RESPAR,RESID,NONKINK}.lean`
with their reports, the checkers `check_W3_identity.py`, `check_W3_statements.py`, `clash_scan_W3.py`.  Compile command
throughout: `cd work/lean && lake env lean ../drafts/moves/<file>.lean`.  Nothing under `work/lean` was written; no `lake build`.
Scripts (both re-runnable from this directory): `assemble_W3D.py` (the merge, the connections, the §A-18 edits — every
operation an exact, unique, asserted string edit; each unit file is first reconstructed from the base and its block,
byte-identity asserted) and `port_R177.py` (the port layout; asserts the verbatim ranges and the fixed statement).
Scratch (probe copies, the scratch object tree of the port test, logs): `…/scratchpad/w3d/`.

## 0. Result in one paragraph

**`W3D_Assembled.lean` (21 748 lines, 1 667 declarations, sha256 `04d99e497b75c5a7…`) compiles: exit 0, 0 errors, 43–56 s,
and contains NO `sorry` (the word occurs 0 times; 0 `declaration uses sorry` warnings; `W3C_Assembled.lean` had 4 terms + 2
prose mentions).**  The OUTER residue `w3cx_outer_residue_data` is CLOSED: RESID's `w3di_outer_residue_proof` (the
identification clause `w3di_ident_at` at the parity's `Λ`) with RESPAR's `w3dp_parity_at_proof` wired in as the body of
RESID's parity black box `w3di_parity_data` (the two Props are alpha-equivalent).  The non-kink leaf
`w3cs_not_kink_site_data` is NOT closed — NONKINK showed it FALSE as stated (W3D_NONKINK_REPORT.md §1) and bypassed it: the
operative chain is rewired to NONKINK's PROVED value form `w3dk_rii_value_sites_data`, and the false leaf, its Prop, its
two consumers and the whole superseded Wave-3b chain are DELETED (§2).  **`#print axioms w3ck_extreme_selected` =
`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness,
SM.ng_finite_word, SM.src_contact]` — exactly the nine registered axioms, no `sorryAx`.**  The port is prepared under
`port/R177/` (three modules, compiled in import order with true module semantics; `RProof.extreme_selected` declared with the
FIXED name and the FIXED statement; the same nine axioms; `PORT_REPORT.md`).  The five frozen blocks are byte-identical; every
skeleton statement is byte-identical except the two deliberately restated `w3g_` sub-leaves (§A-18 item 1) and the deleted
optional `w3b_reparam_switch`; 0 name clashes.

| item | result |
|---|---|
| **`work/drafts/moves/W3D_Assembled.lean`** | 21 748 lines, 1 667 declarations = base 1 427 + RESPAR 70 + RESID 97 (+ the leaf re-declared) + NONKINK 102 + 2 (its chain copies) − 31 deleted (§2) |
| compile | **exit 0, 0 errors**, 43–56 s wall (three runs); 71 warnings = 51 inherited deprecations (`if_pos/if_neg/dif_pos/dif_neg`), 12 unused-variable notes, 7 `unusedSectionVars` notes (RESPAR/RESID), 1 naming note (`w3cs__…`, pre-existing); **0 `declaration uses sorry`** (was 4) |
| `sorry` | `grep -c sorry` **0** (was 6: 4 terms + 2 prose); `#print` / `#eval` 0 |
| `#print axioms w3ck_extreme_selected` | **`propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact`** — no `sorryAx`, no unregistered axiom (§3, `W3D_AXIOMS.log`, 31 declarations) |
| closed leaves | `w3cx_outer_residue_data` (RESPAR + RESID); `w3di_parity_data` (RESID's box := RESPAR's proof) |
| deleted (sorry'd or false, superseded) | `w3b_reparam_switch`, `w3bi_esc_outer_data`, `w3cs_not_kink_site_data` + `w3cs_not_kink_site`, `w3bi_bigon_pair(_of/_data)`, `w3bi_rii_sites(_of/_data)`, the Wave-3b interface Props and replayed ledger, `w3bi_extreme_selected(_leaf)`, the two `w3ck_` conditionals on `w3bi_rii_sites`, 6 library copies — 31 declarations, 727 lines (§2) |
| identity (`check_W3_identity.py`) | 5 frozen blocks **IDENTICAL**; `imports` line `False` (as since Wave 3b; now 4 more imports); `G11_core_sw body starts with sorry: False` |
| statements (`check_W3_statements.py`) | 41/42 skeleton names present (the deleted `w3b_reparam_switch` missing by design); 38 reported byte-identical + 2 checker artifacts (`w3b_isRecordIsoData_of_clauses`, `w3a_X₀_generic`: byte-identical by direct extraction, §4) + the 2 restated `w3g_` sub-leaves; `w3a_` 20/20 |
| clash scan | 1 667 declarations, 0 internal duplicates, **0 fully-qualified clashes** (`clash_scan_W3D.json`); port files 1 091 + 576 + 1, 0 clashes |
| port | **ready**: `port/R177/RProof/GenericTransportSw.lean` (7 845 lines), `RProof/ExtremeSelectedUnits.lean` (13 944), `RProof/ExtremeSelected.lean` (48) + `PORT_REPORT.md`; compiled in import order with a scratch object tree, 0 errors; 0 forbidden strings; `RProof.extreme_selected` on the nine registered axioms (§5) |
| remaining for row 177 | **nothing open in Lean.**  Executor items only (§6) |

## 1. Step (1) — the merge and the two connections

**Blocks (verified).**  `assemble_W3D.py` extracts each unit's insertion and asserts that base + insertion reproduces the
unit file byte for byte: RESPAR = base + lines 16428–17821 (1 394 lines, `/-! ## RESPAR …` to `end W3DP_Config`) after base
16427; RESID = base + `import RProof.ExtremeTransportUnits` (line 8) + lines 16425–18974 replacing base 16424–16426 (the
leaf's docstring / theorem / `sorry`; RESID's 18813 = the base's `sorry`, now `w3di_parity_data`'s; RESID's 18974 = the leaf
re-declared with body `w3di_outer_residue_proof`); NONKINK = base + lines 15509–17090 (1 582 lines, steps 1–7) after base
15508 + lines 18518–18579 (62 lines, step 8) after base 16935.  All three relations hold exactly.

**Order (dependency).**  In `section W3CK_Outer`, base lines 16424–16426 are replaced by RESPAR's block followed by RESID's
block: RESPAR depends only on the Prop `w3cx_outer_residue` and the KNOT/SPLITA/SPLITB material before the leaf (its only
`w3cx_` reference is the Prop, verified), RESID's `w3di_parity_data` needs RESPAR's `w3dp_parity_at_proof`, and the leaf
(RESID's last line) needs RESID's `w3di_outer_residue_proof`.  NONKINK steps 1–7 go before `end W3BI_REAL` as in the unit;
of its step 8 only the two value-form copies are carried, into `section W3CK_Chain` (below).  Imports: the four new lines
8–11 (`RProof.ExtremeTransportUnits` from RESID; `SM.CBProducts`, `CV.SingletonDi`, `SM.ZeroRotationSeed` for §2 (d)).

**Connection (a) — the residue.**  RESID's `def w3di_parity : Prop` and RESPAR's `def w3dp_parity_at : Prop` are both the
residue's binders with the conclusion `∃ Λ : ℕ, (w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q) (transportSupport
hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card = 2 * Λ`, differing only in the binder names `hQi'`/`hS'` vs
`_hQi'`/`_hS'` (alpha-equivalent).  So
`theorem w3di_parity_data : w3di_parity := w3dp_parity_at_proof` (was `by sorry`) type-checks as is, and the leaf
`theorem w3cx_outer_residue_data : w3cx_outer_residue := w3di_outer_residue_proof` (RESID's body: destructure `Λ, hpar` from
`w3di_parity_data`, feed them to `w3di_ident_at`) is sorry-free.  RESPAR's alternative glue `w3dp_outer_residue_of_ident` /
`w3dp_outer_residue_of_homfly` and the Props `w3dp_ident_at` / `w3dp_homfly_at` stay in the file (not consumed; RESID
delivered the full clause with `Λ`).  Docstrings of the two theorems rewritten to describe the proof.

**Connection (b) — the operative chain on the value form.**  In `section W3CK_Chain` the two conditionals on the FALSE Prop
`w3bi_rii_sites` — `w3ck_rii_after_smoothing_weak_occ (hsites : w3bi_rii_sites) …` and `w3ck_esc_interface_ext_of (houter :
w3ck_esc_outer_occ) (hsites : w3bi_rii_sites)` — are replaced by NONKINK's copies `w3dk_rii_after_smoothing_weak_occ
(hsites : w3dk_rii_value_sites) …` and `w3dk_esc_interface_ext_of (houter : w3ck_esc_outer_occ) (hsites :
w3dk_rii_value_sites) : w3ck_esc_interface_ext_occ` (NONKINK lines 18525–18570, verbatim), and the body of
`w3ck_esc_interface_ext_occ_holds : w3ck_esc_interface_ext_occ` becomes
`w3dk_esc_interface_ext_of w3ck_esc_outer_occ_holds w3dk_rii_value_sites_data` (was `w3ck_esc_interface_ext_of
w3ck_esc_outer_occ_holds w3bi_rii_sites_data`).  The terminal `theorem w3ck_extreme_selected : RowShape @ExtremeSelectedData
:= w3ck_esc_ledger w3ck_esc_interface_ext_occ_holds CV.carrierSlotFloor` is unchanged (docstring updated); NONKINK's
redundant duplicates `w3dk_esc_interface_ext_occ_holds` / `w3dk_extreme_selected` are not carried (the `w3ck_` names stay
the operative chain, as the register and the task expect).  Chain now:
`w3ck_extreme_selected := w3ck_esc_ledger w3ck_esc_interface_ext_occ_holds CV.carrierSlotFloor`;
`w3ck_esc_interface_ext_occ_holds := w3dk_esc_interface_ext_of w3ck_esc_outer_occ_holds w3dk_rii_value_sites_data`;
`w3ck_esc_outer_occ_holds := w3ck_esc_outer_occ_of w3ck_split_ident_data`; `w3ck_split_ident_data :=
w3cx_split_ident_of_residue w3cx_outer_residue_data`; `w3cx_outer_residue_data := w3di_outer_residue_proof`;
`w3di_parity_data := w3dp_parity_at_proof`; `w3dk_rii_value_sites_data` (NONKINK: `w3bi_site_data_data` + `w3bi_wall_data_data`
+ `w3dk_reducedValue_of_site` both sides + `w3dk_hrec_free`).  Every input is a proved theorem.

## 2. Step (2) — the port-time statement edits of OPEN_ITEMS §A-18 (and the task's (2)(a)–(d))

**(a) Item 1 — the four restated bigon sub-leaves (RECORDED, nothing to do).**  `w3g_bigonData_smooth_arcST/TS` (Wave-3
skeleton, restated by the W3C assembler with unit G's non-kink hypothesis, `-- (W3C assembler) STATEMENT RESTATED` at the
assembled lines 9246 / 9276) and `w3bi_bigonData_smooth_arcST/TS_switch_z` (Wave 3b, restated likewise, lines 12924 / 12946)
carry the hypothesis `hkink` and are PROVED (standard axioms).  `check_W3_statements.py` reports exactly the two `w3g_` names
as differing from `Skeleton_W3.lean` (the `w3bi_` two are not skeleton names).  In this wave the hypothesis is DISCHARGED where
it holds (`w3dk_reducedValue_of_notKink`) and BYPASSED where it fails (`w3dk_reducedValue_of_kink`, the flat subdivision), so
the restated forms are the right ones and stay.  To record in AUTHOR_NOTES / FINAL_REVIEW §5 as the rule-3 finding it is.

**(b) Item 2 — the superseded Wave-3b chain (DELETED; task option "delete them").**  Deleted, with exact unique markers and
the declared names asserted (`assemble_W3D.py` §5), 31 declarations / 727 lines, none of them consumed by the surviving code
(asserted: no remaining reference outside comments; compile 0 errors):

| region (base lines) | declarations | why |
|---|---|---|
| 4086–4096 | `w3b_reparam_switch` | optional skeleton sub-leaf, `sorry`, no consumer (task: "delete it too if unused") |
| 10579–10670 | `w3bi_knot_after_two`, `w3bi_three_components`, `w3bi_esc_MoveDataWeak`, `w3bi_esc_interface_ext`, `w3bi_esc_outer` | the Wave-3b Props: the two outer clauses quantify over every relational `IsOrientedSmoothing` (KNOT rule 3, not provable as stated); superseded by `w3ck_esc_MoveDataOcc` / `w3ck_esc_interface_ext_occ` / `w3ck_esc_outer_occ` |
| 11688–11691 | `w3bi_esc_outer_data` | the frozen OUTER leaf, `sorry`, not provable as stated |
| 12765–12857 | `w3bi_rii_sites`, `w3bi_bigon_pair` | FALSE as stated in the kink configuration (NONKINK §1.3: they assert a `BigonData` on the switched smoothing whose run component is the 4-gon) |
| 13714–13764 | `w3cs_not_kink_site`, `w3cs_not_kink_site_data`, `w3bi_bigon_pair_of`, `w3bi_bigon_pair_data` | SITE's non-kink box: FALSE as stated (§A-17, NONKINK §1.2), `sorry`; its conditional consumer and its assertion |
| 14296–14673 | `w3bi_rii_sites_of`, `w3bi_rii_sites_data`, `w3bi_rii_after_smoothing_weak`, `w3bi_esc_interface_ext_of`, `w3bi_esc_interface_ext_holds`, `w3bi_esc_contact_identity`, `w3bi_esc_couple`, `w3bi_esc_ledger`, `w3bi_extreme_selected`, `w3bi_extreme_selected_leaf` | the Wave-3b site chain (conditionals on the false Props), the replayed Wave-3b ledger (byte-faithful copies of `esc_*`, consumed only by `w3bi_extreme_selected`; the operative chain has its own copies `w3ck_esc_contact_identity` / `w3ck_esc_couple` / `w3ck_esc_ledger`) and the Wave-3b terminal + its leaf-shaped instance |
| 16606–16659 (replaced, §1 (b)) | `w3ck_rii_after_smoothing_weak_occ`, `w3ck_esc_interface_ext_of` | conditionals on `w3bi_rii_sites` |

Kept and operative: `w3cs_NotKink`, `w3cs_not_kink_arcST/TS` (the non-kink predicate, used by `w3bi_bigon_of_site` and
NONKINK), `w3bi_switch_riii`, `w3bi_site_data(_data)`, `w3bi_wall_data(_data)`, `w3bi_hrec_general`, `w3bi_bigon_of_site(_model)`,
the restated `w3bi_bigonData_smooth_*_switch_z`.  The W3BI_REAL header docstring was rewritten to describe this (the only
docstring edit outside the connected declarations); other unit docstrings that mention the deleted names in prose
("at the binders of `w3bi_esc_outer`", "the black box `w3bi_esc_outer_data`") are left as historical unit prose, as the
row-174/176 ports did.

**(c) Item 3 — the prose mentions (REWORDED).**  Exactly the two lines the register names: base 7856 (unit G's header,
"their remaining `sorry` is the hypothesis `hk5` alone" → "their remaining obligation is the hypothesis `hk5` alone") and
base 14706 (SPLITB's header, "(one `sorry`, `w3cb_split_core_data`; …)" → "(`w3cb_split_core_data`, left open by this unit
and since proved from the residue; …)").  The register's warning that the third mention "16561" is stale was right: section
`W3CK_Chain` contains none.  The `-- (W3C assembler) STATEMENT RESTATED` comments name no forbidden word and stay.  The three
unit blocks contain no occurrence.  Result: `grep -c sorry` = 0.

**(d) §7 (c) — the library copies (DROPPED by importing; compiles).**  Imports added: `SM.CBProducts`, `CV.SingletonDi`,
`SM.ZeroRotationSeed` (none has a global instance or notation; all built).  Deleted copies and the renamed uses (regex on the
identifier, counts include prose):
`w3bh_restrictCrossings_iso_of_recordIso` → `CB.restrictCrossings_iso_of_recordIso` (SM/CBProducts.lean 1358; 9 uses, 6 in
unit H / REAL + 3 in NONKINK); `w3cb_insert_eq` → `CV.cvt165s_insert_eq` (CV/SingletonDi.lean 238; 5); `w3cc_principalAngle_swap`
(+ its helper `w3cc_principalAngle_neg_neg`) → `principalAngle_swap` (SM/ZeroRotationSeed.lean 16; 1); `w3cc_rot_ray` →
`CV.cvt165s_rot_ray` (SingletonDi 151; 1) and `w3cc_uniformOrOneDissent_of_pattern` → `CV.cvt165s_uniformOrOneDissent_of_pattern`
(SingletonDi 180; 3) — the library's two take the pattern hypothesis as the literal disjunction, `w3cc_Pattern L τ` unfolds to
it, and the applications elaborate.  NOT dropped: `w3cs_exact_symm` (= `s174_exact_symm`, which would need
`import RProof.GenericSelectedUnits`, not among the three named modules; 1 use) and KNOT's K2 record lemmas (their original is
the draft `R176_SMOOTH` §R1, not a module).  The `w3cc_sign_principalTurn` / `w3cc_principalTurn_reversal` copies stay (still
consumed by the `w3cc_` rotation lane).

## 3. Step (3) — compile and `#print axioms`

`cd work/lean && lake env lean ../drafts/moves/W3D_Assembled.lean`: exit 0, 0 errors, 43 s (final file; 56 s on the first
build), 71 warnings as in §0, no `declaration uses sorry`.  Scratch copy `…/scratchpad/w3d/W3D_Axioms_scratch.lean` = the file
+ 31 `#print axioms` lines before the final `end SM.Link` (exit 0, 46 s; output `W3D_AXIOMS.log` next to this report):

| declaration | axioms |
|---|---|
| **`w3ck_extreme_selected`** | **`propext, Classical.choice, Quot.sound, lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact`** (printed inside `namespace SM.Link`, hence without the `SM.` prefix; the port probe prints `SM.lit_homfly` etc.) — **no `sorryAx`** |
| `w3ck_esc_interface_ext_occ_holds`, `w3ck_esc_outer_occ_holds`, `w3ck_split_ident_data`, `w3cb_split_core_data`, **`w3cx_outer_residue_data`**, `w3di_outer_residue_proof`, `w3di_ident_at`, `w3di_ident_abstract`, **`w3dk_rii_value_sites_data`**, `w3dk_reducedValue_of_site`, `w3dk_esc_interface_ext_of`, `w3ck_esc_ledger`, `w3ck_esc_couple`, `w3bi_switch_riii`, `G11_core_sw`, `esc_switch_riii_of_chain`, `w3e_strong_case_sw` | `propext, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness` |
| `w3dk_rii_after_smoothing_weak_occ`, `w3cx_split_ident_of_residue` | standard + `lit_homfly` |
| **`w3di_parity_data`**, **`w3dp_parity_at_proof`**, `w3dp_twoLambda_eq_card_mixedSet`, `w3bi_site_data_data`, `w3bi_wall_data_data`, `w3bi_bigon_of_site`, `w3cx_fullSplitData_at`, `w3cx_sign_table_at`, `w3ca_split_config`, `w3ck_knot_after_two`, `w3ck_three_components_count` | `propext, Classical.choice, Quot.sound` |

No unregistered axiom anywhere; the three literature axioms beyond the ledger's reads (`lit_homfly_descent`, `ng_finite_word`,
`src_contact`) enter only through `CV.carrierSlotFloor`, exactly as for rows 174 and 176.  The criterion of task item (3) is
met, so the port (item (4)) was prepared.

## 4. Step (5) and the other checks

* `check_W3_identity.py Port_GenericTransportSw_draft.lean W3D_Assembled.lean`: `structure G11_ConfigSw` (1206 B), the
  `namespace G11_ConfigSw` block (1252 B), `def G11_core_sw_statement` (1015 B), the statement of `theorem G11_core_sw`
  (136 B), `theorem esc_switch_riii_of_chain` (694 B) — all **IDENTICAL**; `imports` line `False` (inherited since Wave 3b's
  `RProof.RALedgers`; now also the four new imports); `G11_core_sw body starts with sorry: False` (proved).  The same five are
  IDENTICAL in the port module `GenericTransportSw.lean`.
* `check_W3_statements.py W3D_Assembled.lean`: 42 skeleton statements, 41 in the target — `w3b_reparam_switch` missing BY
  DESIGN (deleted, §2 (b)).  Reported "differing": `w3g_bigonData_smooth_arcST/TS` (the deliberate restatements, §2 (a)) and
  `w3b_isRecordIsoData_of_clauses`, `w3a_X₀_generic` — the latter two are a checker ARTIFACT: the checker's regex runs from a
  `theorem w3…` to the next `:= by`; `w3b_isRecordIsoData_of_clauses` is term-mode, and in the base its match ended at the
  `:= by` of `w3b_reparam_switch` (base 4093); with that line deleted the match runs on to `w3a_X₀_generic`'s own `:= by` and
  swallows that declaration.  Direct extraction of both statements (from `theorem` to the first `:=`) shows them byte-identical
  to `Skeleton_W3.lean` and to `W3C_Assembled.lean`.  `w3a_` count 20/20.
* `clash_scan_W3.py ../../lean W3D_Assembled.lean`: 1 667 declarations, 1 667 distinct fully-qualified names, 0 internal
  duplicates, **0 fully-qualified clashes**; 925 informational short-name coincidences, all the inherited
  `SM.Link.G11_ParamsSw.gu*_` ↔ `RProof.G11_Params.gu*_` ones (`clash_scan_W3D.json`).  Port files: 1 091 / 576 / 1
  declarations, 0 clashes each (`clash_scan_W3D_row.json` = the row file's scan).  `RProof.extreme_selected` is declared
  nowhere in `work/lean`.
* Byte-identity outside the edits: `difflib` between `W3C_Assembled.lean` and `W3D_Assembled.lean` gives exactly 36 hunks —
  the 4-line import insertion, the 3 unit insertions/replacements (base 15508 +1 582; base 16424–16426 → 3 945 lines; the
  W3CK_Chain replacement 16606–16659 in 6 hunks), the 11 deletions of §2 (b)/(d), the 2 prose rewordings, the W3BI_REAL
  header, the two docstring rewrites (`w3ck_extreme_selected`, the leaf), and the 15 single-line renames of §2 (d).
  Nothing else differs; no global reformatting.

## 5. Step (4) — the port (`port/R177/`, see `port/R177/PORT_REPORT.md`)

| file | lines | md5 | content | compile (scratch object tree, module semantics) |
|---|---|---|---|---|
| `RProof/GenericTransportSw.lean` | 7 845 | `48c20b3a10e888e6d73d12295ffb4488` | 10 header lines (new) + assembled 1–7 (the skeleton's seven imports) + assembled 12–7835 verbatim (the skeleton docstring, `namespace SM.Link / open SM / noncomputable section`, `section RIIISw … end RIIISw`, `esc_switch_riii_of_chain`) + `end / end SM.Link` (new); 1 091 declarations | exit 0, 0 errors, 24 inherited deprecation warnings, ≈ 47 s; olean 14 MB |
| `RProof/ExtremeSelectedUnits.lean` | 13 944 | `044adb975705c505175942defde89f6e` | 11 header lines (new) + `import RProof.GenericTransportSw`, `RProof.ExtremeTransportUnits`, `SM.CBProducts`, `CV.SingletonDi`, `SM.ZeroRotationSeed` + a new module docstring + the frame + assembled 7837–21748 verbatim (`section Row177_6`, `section W3BI_REAL` incl. NONKINK, `section W3CK_KNOT` incl. RESPAR/RESID and the chain, `end / end SM.Link`); 576 declarations, all `w3*_`-prefixed in `SM.Link` | exit 0, 0 errors, 47 warnings (inherited), ≈ 47 s; olean 26 MB |
| `RProof/ExtremeSelected.lean` | 48 | `19a38268571df9d7f7488bd426a88a39` | 7 header lines + `import RProof.ExtremeSelectedUnits` + `namespace RProof / open SM SM.GeoCarrier / variable {n : ℕ} [NeZero n]` + docstring quoting the printed obligation (X1Rows.lean 1742–1753) + `theorem extreme_selected … := SM.Link.w3ck_extreme_selected n hn E e f g h3 h4e h4f h4g hE` | exit 0, 0 errors, 0 warnings, ≈ 24 s |

The seven statement lines of `extreme_selected` are byte-identical to `work/drafts/cvtail/Statements_FINAL.lean` 803–809 (minus
the trailing ` by`) and to `RProof/ExtremeTransport.lean` 39–45 after `extreme_transport ↦ extreme_selected`,
`ExtremeTransportData ↦ ExtremeSelectedData` (both asserted by `port_R177.py`).  Probe (`…/scratchpad/w3d/R177Probe.lean`,
`import RProof.ExtremeSelected`; output `port/R177/probe_port.log`): **`'RProof.extreme_selected' depends on axioms:
[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness,
SM.ng_finite_word, SM.src_contact]`**; `#check @RProof.extreme_selected` prints the `RowShape` body.  Strings `sorry`,
`#print`, `#eval`: 0 in every file under `port/R177/` (the probe lives in the scratchpad).  Recipe and `port_chain.log`: PORT_REPORT §2.

## 6. Notes for the executor, AUTHOR_NOTES and FINAL_REVIEW

1. **Row 177 is closed on the registered axioms** (`RProof.extreme_selected`, fixed name and statement).  Land: copy the three
   files of `port/R177/RProof/` into `work/lean/RProof/`, date the `<HH:MM>Z` placeholders, `lake build`, map the
   `R:extreme_selected` entry of `lean-declarations.json` to `RProof.extreme_selected` / `RProof.ExtremeSelected`, statement
   review per the rows' protocol.  Then §A-19 (row 178 `RProof.cv_R`, the staged one-liner), row 183 (`Bridge.sm_R`), row 184.
2. **Register.** §A-15: closed.  §A-16: closed — clause (i) RESPAR (`w3dp_parity_at_proof`, standard axioms: the bridge
   `2Λ(J_L) = #mixedSet` + mp:zero-link), clause (ii) RESID (`w3di_ident_at`, registered axioms through `r176s_homfly_of_liftBlock`
   / `r176c_homfly_of_liftBlock_curl` / `r176s_homfly_eq_groupedPoly`); the residue was TRUE as stated.  §A-17: closed as
   "**not a consequence of the configuration data; not needed**": NONKINK's derivation attempt (audit A-177-NK-1, W3D_NONKINK_REPORT
   §1) shows `w3cs_not_kink_site` FALSE as stated (the monogon `e → e+1 → e+2 = f` cut by `g` is a genuine 177 configuration);
   the (6) content is realised in the value form `w3dk_rii_value_sites_data` (kink case by a flat subdivision of the carrier
   polygon); **no event-level hypothesis was added, FR-R-177-K does not arise**, no accepted event vocabulary touched.  §A-18:
   items 1–3 done as in §2; the `w3bi_` chain deleted (option "delete"), the library copies dropped by importing.
3. **Rule-3 findings to record** (statements found false / unprovable as stated in draft material, none a row statement):
   (i) the four `j = 2` bigon sub-leaves (Wave 3c, restated with the non-kink hypothesis); (ii) `w3bi_knot_after_two` /
   `w3bi_three_components` / `w3bi_esc_outer` (relational smoothings; replaced by the record-clause `w3ck_` forms);
   (iii) `w3cs_not_kink_site`, `w3bi_bigon_pair`, `w3bi_rii_sites` (false in the kink configuration; replaced by
   `w3dk_rii_value_sites`).  All three sets are now deleted from the assembled file and the port.  No kernel counterexample
   was built (draft leaves, not row statements — package rule for `work/repairs/` not triggered).
4. **G-03 (`RProof.G11_Config.trans`)**: route (ii) taken — the additive trans-free copy `G11_ConfigSw` / `G11_ParamsSw` is
   ported as `RProof/GenericTransportSw.lean`; the accepted `RProof/GenericTransport.lean` is untouched; no checker re-run of
   accepted rows is needed for this.
5. **Not done here (deliberately, verbatim port first):** the optional refactors of PORT_REPORT §5 item 5 (NONKINK's bigon-free
   `w3dk_hrec_free` replacing `w3h_hrec`, library-grade material to shared homes, `w3cs_exact_symm` by importing
   `RProof.GenericSelectedUnits`); a prune of helpers left unconsumed by the deletions, if any (the compile does not report them).

## 7. Pitfalls / notes

* `grep -c` exits 1 when it counts zero matches — never chain it with `&&` (cost one no-op compile round here).
* The word `sorryAx` contains the forbidden substring: the port headers must say "no placeholder axiom" (caught by
  `port_R177.py`'s own assertion).
* `check_W3_statements.py` cannot be trusted for term-mode skeleton theorems once a following `:= by` line disappears (§4);
  verify statements by extracting `theorem … :=` directly.
* The alpha-equivalence of RESID's `w3di_parity` and RESPAR's `w3dp_parity_at` made the connection a one-token body; had the
  binder ORDER differed, the bridge would have been an `intro`/`exact` wrapper — check the two Props' text before wiring.
* Placing RESPAR's block before RESID's (both inside `section W3CK_Outer`, both before the leaf) is what lets `w3di_parity_data`
  see `w3dp_parity_at_proof`; RESPAR's own placement (after the leaf) would not.
* Times (UTC / ET): 07:33 / 3:33am start (author response, the three reports, W3C §7, the R174/R176 port reports, the
  boundaries); 07:44 assembler written; 07:45–07:46 first compile (0 errors, 56 s); 07:48 normalisation removed, recompile
  43 s; 07:49 axioms probe 46 s; 07:52 port files; 07:52–07:56 port chain (47 + 47 + 24 s + probe 23 s); 08:00–08:05 header
  fix, port chain re-run; 08:10 / 4:10am ET this report.
