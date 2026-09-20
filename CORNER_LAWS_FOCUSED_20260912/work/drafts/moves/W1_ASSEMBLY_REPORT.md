# W1_ASSEMBLY_REPORT — assembly of the moves toolkit, Wave 1

Assembler (subagent), 2026-09-15 20:15 UTC / 4:15pm ET.  Inputs: `Skeleton_W1.lean` (1866 lines, 33 `sorry`
declarations), the seven unit files `W1_M1 … W1_M7.lean` with their reports, `Statements_FINAL.lean` (frozen),
`check_W1_identity.py`.  Compile command throughout: `cd work/lean && lake env lean ../drafts/moves/<file>.lean`
(Lean 4.34.0-rc2 toolchain of `work/lean`).  Nothing under `work/lean` was written.

## 0. Deliverables and checks

| item | result |
|---|---|
| **`work/drafts/moves/Moves_Assembled.lean`** | **5470 lines**, 489 declarations (skeleton 267 + 222 unit helpers after de-duplication) |
| compile | **exit 0, 0 errors**, ≈ 15 s; warnings: 1 `declaration uses sorry` (line 5422 = `G11_core_sw`) + the skeleton's inherited cosmetic `<;>` linter warning (now line 1384) |
| `grep -c sorry Moves_Assembled.lean` | **2** = the frozen header comment (line 17 "Every `sorry` is a LEAF …") + the ONE remaining body (line 5423, `G11_core_sw`) |
| `#print axioms` (scratch copy, §4) | the nine named declarations: standard axioms + the registered literature axioms only; **no `sorryAx`** anywhere except `G11_core_sw` itself |
| statement byte-identity (§5) | `check_W1_identity.py`: **37/37** declarations of `Statements_FINAL.lean` byte-identical (changed/missing: 0); every line of `Statements_FINAL.lean` except its five leaf `sorry` bodies appears in order in the assembled file |
| name clashes against `work/lean` (§6) | **0** fully-qualified clashes among 489 declarations; 61 informational short-name coincidences in other namespaces |
| unproved Wave-1 sub-leaves (§3) | **none** — all 29 `m1_…m6_` sub-leaves and 3 of the 4 frozen leaves are closed; only the Wave-3 leaf `G11_core_sw` remains a `sorry` (by design) |
| port drafts (§7) | `Port_BigonDeletion_draft.lean` (5374 lines, exit 0, **no `sorry` declaration**) and `Port_GenericTransportSw_draft.lean` (120 lines, exit 0, the one leaf) — the split compiles, the two halves are independent |
| scripts | `assemble_W1.py` (diff validation + hunk application + de-duplication; `python3 assemble_W1.py .` regenerates the file), `clash_scan_W1.py` |

## 1. Diff verification of the seven unit files against `Skeleton_W1.lean`

Method: `difflib` line diff of each `W1_M*.lean` against the skeleton (also `diff` by hand); every opcode
classified.  Rule: a hunk is clean iff it (a) removes only a `sorry` body line (or re-emits a sub-leaf's own
statement line unchanged up to `:=` with a term body), and (b) adds only declarations named `um<N>_…` plus
comments / blank lines / `variable (B) in`.  No `delete` opcode, no `namespace`/`section`/`end`/`open`/
`set_option`/`attribute` line, no docstring or statement edit was found in any unit.

| unit | hunks (skeleton lines) | removed skeleton lines | sub-leaves whose `sorry` was replaced | helpers added | `check_W1_identity.py` |
|---|---|---|---|---|---|
| M1 | `456a`, `464c` | 1 × `  sorry` | `m1_exists_cut` (464) | 42 `um1_*` | pass |
| M2 | `1089a`, `1094c 1102c 1111c 1117c` | 4 × `  sorry` | `m2_regular m2_tail_off m2_transverse m2_no_triple` | 33 `um2_*` | pass |
| M3 | `1125a`, 9 × `c` | 9 × `  sorry` | `m3_isCrossing_orig m3_kind_ne_mid m3_orig_injOn_crossing m3_origCrossing_ne_y m3_origCrossing_ne_z m3_crossingPoint_origCrossing m3_origCrossing_injective m3_exists_lift m3_crossingParam` | 28 `um3_*` | pass |
| M4 | `1333a`, 11 × `c` | 11 × `  sorry` | `m4_arcIn_ne_arcS m4_arcIn'_ne_arcS' m4_arcCover m4_arcCover' m4_clean m4_clean' m4_inner_iff' m4_no_inner m4_sep_y m4_sep_z m4_same_over` | 60 `um4_*` (11 with `variable (B) in`) | pass |
| M5 | `1409a`, `1415,1416c` | the statement line `theorem m5_moveMatch : … := by` + `  sorry` | `m5_moveMatch` — re-emitted as `theorem m5_moveMatch : Nonempty (MoveMatch C.U (B.reducedDiagram C) D) := ⟨um5_moveMatch C⟩` (statement text up to `:=` identical) | 35 `um5_*` (incl. 3 `noncomputable def`) | pass |
| M6 | `114a 122c 125a 135c 1459c 1514a 1519c 1527c` | 5 × `  sorry` | `reducedRecord_counts` (122), `Record.restrictCrossings_switch` (135), `m6_exists_origVisit`, `m6_key_lt_iff`, `m6_succ` | 30 `um6_*` (incl. 5 `def`) | 37/37 statements pass; **prefix check False** — expected and legitimate: the two frozen record leaves sit inside lines 1–136 and M6 inserted its helpers before them and replaced their bodies; the checker's line-range prefix test cannot distinguish this from a violation, the diff can (only `sorry` lines removed) |
| M7 | `1593a`, `1608c` | 1 × `  sorry` | `exists_bigonData_of_triangle` (1608) | 2 `um7_*` | 37/37 statements pass; **suffix check False** — expected: the checker allows only `exists_rii_deletion`'s body to change in the suffix, and M7 legitimately closed `exists_bigonData_of_triangle` there |

Verdict: **all 41 hunks are clean; no violation; nothing withheld.**  Every removed line is exactly a sub-leaf
`sorry` of the unit that owns it (mapped by declaration in `assemble_W1.py`), every added declaration carries
the unit prefix.  No two units touch the same skeleton line (M1 456/464 · M6 114–135, 1459–1527 · M2 1089–1117
· M3 1125–1254 · M4 1333–1387 · M5 1409–1416 · M7 1593–1608), so contiguity is trivial and hunks were applied
in skeleton order.

## 2. Assembly

`assemble_W1.py` (kept next to this report) recomputes the seven diffs, validates them as in §1, aborts on any
violation, applies the 41 hunks in skeleton order, then runs a **de-duplication** pass.  By *name* nothing
was duplicated (the prefixes `um1_ … um7_` are disjoint; 0 internal duplicates, 0 renames needed).  By
*statement* 8 helper pairs were byte-identical (same binder context checked: the um2/um3 pairs share
`variable {B} (C : B.Cut)`; `um4_s_ne_strand` had `variable (B) in`, matching `um1_s_ne_strand`'s explicit
`B`; `um2_not_adjacent_eIn_eOut`'s only use is dot-notation `B.…`, so the explicit-`B` twin fits).  The later
twin was removed (declaration, docstring, `variable (B) in`) and its uses renamed:

| dropped (later) | kept (earlier) | lines removed | use lines renamed |
|---|---|---|---|
| `um3_adjacent_iff` | `um2_adjacent_iff` | 18 | 5 |
| `um3_strand_succ_j` | `um2_strand_succ_j` | 3 | 5 |
| `um3_strand_pred_j` | `um2_strand_j_sub_one` | 5 | 1 |
| `um3_seg_subset_seg_orig` | `um2_seg_subset_seg_orig` | 15 | 4 |
| `um3_mid_seg_subset_U` | `um2_seg_mid_subset_U` | 10 | 1 |
| `um3_cutIn_disjoint_cutOut` | `um2_cutIn_disj_cutOut` | 22 | 2 |
| `um4_s_ne_strand` | `um1_s_ne_strand` | 12 | 1 |
| `um2_not_adjacent_eIn_eOut` | `um1_not_adjacent_in_out` | 12 | 1 |

Union before de-duplication: 5567 lines, 497 declarations (compiled clean too); after: 5470 lines, 489.
Two further statement-identical pairs were deliberately KEPT because one side is a skeleton API name:
`um6_y_ne_z` (line 117, needed before the record leaf) ≡ `y_ne_z` (400), and `um6_crossKeep_keep_iff` (140) ≡
`crossKeep_keep_iff` (4527); the port may turn the API proofs into one-liners.

Layout of the assembled file (line numbers): `## 1` bigon site 39 · `### 1b` record companions 113 (leaves
`reducedRecord_counts` 191, `Record.restrictCrossings_switch` 262, both PROVED) · `## 1c` API 269 (`Cut` 453,
`m1_exists_cut` 1203, kinds 1285, reduced shadow 1472, kind laws 1584, `section Construction` 1902: M2 1909–2472,
`m2_generic` 2467, M3 2473–3068, `reducedDiagram` 3008, M4 3069–4117, M5 4118–4504, `m5_moveMatch` 4503, M6
4505–4956, `recordIso` 4945, M7 assembly 4957: `m7_riiData` 4961, `m7_rii` 4986) · `## 2` `exists_rii_deletion`
5001, `## 2a` um7 helpers 5008, `exists_bigonData_of_triangle` 5066 · `## 3` glue 5230 · `## 4` row 177 (4)
5343–5436 (`G11_ConfigSw` 5352, `G11_core_sw_statement` 5412, `G11_core_sw` 5422 = the `sorry`,
`esc_switch_riii_of_chain` 5430) · `## 5` avoidances 5437 · `end SM.Link` 5470.

## 3. Unproved sub-leaves

**None.**  All 29 Wave-1 sub-leaves (`m1_exists_cut`; `m2_regular m2_tail_off m2_transverse m2_no_triple`;
nine `m3_*`; eleven `m4_*`; `m5_moveMatch`; `m6_exists_origVisit m6_key_lt_iff m6_succ`) are proved, and so are
three of the four frozen leaves (`exists_bigonData_of_triangle`, `BigonData.reducedRecord_counts`,
`Record.restrictCrossings_switch`); `exists_rii_deletion` was already proved in the skeleton from them.  The
only `sorry` body left is the **frozen Wave-3 leaf `G11_core_sw`** (row 177 (4)), which was never a Wave-1
target.  No proving by the assembler was needed.

## 4. Compile and axioms

Compile of `Moves_Assembled.lean`: exit 0, 0 errors, ≈ 15 s (load ≈ 8 cores).  `#print axioms` was run on a
scratch copy (`<scratchpad>/Moves_Axioms.lean` = the file + `#print axioms` lines; no `#print`/`#eval`/`#check`
exists in the deliverable):

| declaration | axioms |
|---|---|
| `exists_rii_deletion`, `exists_bigonData_of_triangle`, `rii_deletion_counts`, `s7_rii_witnesses` | `propext, Classical.choice, Quot.sound` |
| `gsc_fulltwist_of_bigon`, `est_port_weak_of_bigon`, `fulltwist_coefficient_of_port_weak` | standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` |
| `two_component_row_of_recordIso`, `curl_block_value` | standard + `SM.lp_lm` |
| `BigonData.reducedRecord_counts`, `Record.restrictCrossings_switch`, `BigonData.m1_exists_cut`, `m2_generic`, `reducedDiagram`, `m5_moveMatch`, `m6_recordIso`, `m7_rii` | standard only |
| `s7_switch_value_of_bigon` | standard + `SM.lp_lm` |
| `fulltwist_skein_of_port_weak`, `esc_rii_after_smoothing_of_bigons`, `esc_switch_riii_of_chain` | standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` |
| `G11_core_sw` | `propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly` — the open leaf itself |

`SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` are the registered literature axioms of
`work/lean/axiom-policy.json` (`lit:homfly`, `lp:lm`, `lp:lm-uniqueness`).  **No `sorryAx` reaches any
declaration through any sub-leaf**; `esc_switch_riii_of_chain` is also `sorryAx`-free (it consumes the
G11 output as hypotheses and never calls `G11_core_sw`).  The decisive test of PLAN_FINAL §5 ("`s7_rii_witnesses`,
`gsc_fulltwist_of_bigon`, `est_port_weak_of_bigon` sorry-free with `exists_rii_deletion` closed, axioms =
standard + `lp_lm` / `lit_homfly`") therefore **passes** on the assembled file.

## 5. Statement byte-identity with `Statements_FINAL.lean`

`python3 check_W1_identity.py Statements_FINAL.lean Moves_Assembled.lean`: "declarations in Statements_FINAL:
37; changed/missing: 0".  Its two range checks report False for the reasons of §1 (M6's helpers and two closed
leaves inside lines 1–136; M7's closed leaf in the suffix), so a stronger check was run: with the five leaf
`sorry` lines (Statements_FINAL 122, 135, 150, 166, 377) removed, **every remaining line of
`Statements_FINAL.lean` occurs, in order, in the assembled file** (0 missing).  Hence no statement, docstring,
attribute, `variable`, `open` or section line of the frozen file changed; only the four leaf bodies did.

## 6. Name-clash scan (`clash_scan_W1.py`)

All 489 declarations of the assembled file, with their namespaces resolved from `namespace`/`end` nesting,
against every declaration of `work/lean/**/*.lean` (SM, CV, RProof, Bridge, Supplemental; `.lake` excluded):
**0 fully-qualified clashes.**  The 61 short-name coincidences live in OTHER namespaces and are harmless
inside the file (it opens only `SM`, `RProof` (§4) and `scoped Classical`); they are worth knowing for
consumers: `SM.Link.BigonData.{origCrossing, orig_mem_origCrossing, crossingEquiv, arcS, origPt, origVisit,
origVisit_fst, origVisit_injective, visitEquiv, compOf_origVisit, twin_origVisit, overBit_origVisit,
sign_origVisit, key}` and `SM.Link.BigonData.Kind.*` mirror `SM.Link.Smoothing.*` / `Smoothing.StrandKind.*`
by design (same template), so a consumer that `open`s both `SM.Link.Smoothing` and `SM.Link.BigonData` will
hit ambiguous identifiers — qualify or open one.  `SM.Link.G11_ConfigSw.{comp, vmp, vpm, vmq, vqm, vpq, vqp, σ, σD}`
mirror `RProof.G11_Config.*` (section 4 does `open RProof`; no ambiguity arose because the fields are
accessed by dot-notation).

## 7. Port plan

**Target modules** (PLAN_FINAL §3 library homes): `work/lean/SM/BigonDeletion.lean` for everything
sorry-free, `work/lean/RProof/GenericTransportSw.lean` for row 177 (4).  The lakefile glob (`SM.+`, `RProof.+`)
picks both up automatically; nothing to add to `Supplemental.lean`.  The split was TESTED here:

* **`Port_BigonDeletion_draft.lean`** (5374 lines) = the assembled file minus `## 4` (lines 5343–5436:
  `section RIIISw` … `end RIIISw` and `esc_switch_riii_of_chain`) with a reworded module header.  Compiles:
  exit 0, **no `sorry` declaration** (the two textual `sorry` hits are in the header prose).  Contents: `## 1`
  site + `1b` record companions (both leaves proved), `## 1c` construction, `## 2` constructor + `2a` triangle
  builder, `## 3` glue for 110 / 174 / 176 / 177 (6) (`s7_rii_witnesses`, `s7_switch_value_of_bigon`,
  `moves_fulltwist_triple`, `gsc_fulltwist_of_bigon`, `est_port_weak`, `est_port_weak_of_bigon`,
  `fulltwist_skein_of_port_weak`, `fulltwist_coefficient_of_port_weak`, `esc_rii_after_smoothing_of_bigons`,
  `rii_deletion_counts`), `## 5` avoidances.
* **`Port_GenericTransportSw_draft.lean`** (120 lines) = `G11_ConfigSw`, `G11_core_sw_statement`, the leaf
  `G11_core_sw` (**stays `sorry`; must NOT be ported to `work/lean` until Wave 3 closes it**) and
  `esc_switch_riii_of_chain`.  Compiles standalone (exit 0, the one `sorry`) with the same five imports and
  **without** importing the constructor: the two halves are independent.  Note for the executor:
  `esc_switch_riii_of_chain` is PROVED and `sorryAx`-free (it uses only `CV.gausscode_polynomial`), so it could
  be ported at once next to the constructor if row 177 (4)'s consumer wants it before Wave 3; it was kept with
  the G11 material as instructed.

**Imports** of `SM/BigonDeletion.lean`: `SM.Smoothing`, `SM.MarkedProducts`, `SM.SingleCrossing`,
`CV.FullTwist`, `RProof.GenericTransport` — exactly the skeleton's header.  Measured dependency on
`RProof.GenericTransport`: compiling the portable half without that import fails at exactly four identifiers,
all in the triangle builder (`## 2a` / `exists_bigonData_of_triangle`): `RProof.gu2_det_smul_smul`
(GenericTransport:9101, 2 lines) and `RProof.gu2_mem_segment_{ab,bc,ac}_of_line` (9235–9254, resting on the
affine-basis toolkit `gu2_mem_tri_iff` / `gu2_mem_segment_of_coord{0,1,2}`, ≈ 170 lines 9093–9259).  Two
options: (i) keep the import (no cycle: `RProof.GenericTransport` imports `RProof.X1Rows3`, `SM.CS3`, Mathlib;
nothing imports the new module) — an `SM.*` module importing `RProof.*` and `CV.*` inverts the usual layering
(SM → CV → RProof), but `Statements_FINAL.lean` itself was frozen with these imports; or (ii) copy the four
`gu2_*` lemmas with their ≈ 170-line toolkit into `SM/BigonDeletion.lean` under a local prefix and drop
`RProof.GenericTransport` (then the module depends on RProof only through nothing; `CV.FullTwist` stays for
`## 3`, `SM.SingleCrossing` for `curl_block_value`).  If layering matters to the reviewers, (ii); otherwise (i)
is a one-line import and byte-faithful.  `RProof/GenericTransportSw.lean` needs `RProof.GenericTransport`
(`G11_triangle`, `edgeSegment`, `G11_Config` vocabulary) and `CV.FullTwist` (`CV.gausscode_polynomial`).

**Lines to reword in the port** (no `#print` / `#eval` / `#check` exists in any of the three files):
* the header docblock of the assembled file (lines 7–31): "`# Statements_FINAL`", the `Check:` line (15), and
  the paragraph "Every `sorry` is a LEAF … (17–22)" — four of its five listed leaves are now proved; the port
  drafts already carry a rewritten header (see `Port_BigonDeletion_draft.lean` 7–28);
* `## 1c` header (assembled 269–288; draft 266–285): "the sub-leaves of units U-M1 … U-M7", "Everything in
  this section is NEW relative to `Statements_FINAL.lean`" (draft line 268), "Sub-leaves are named `m<unit>_…`";
* 31 docstrings opening with `**Sub-leaf (U-Mn).**` / `**Leaf …**` (draft lines 185, 253, 1194, 2151, 2255, 2377, 2453, 2463, 2723 …, 4951; the same
  docstrings in the assembled file at 188, 256, 1197, 2154, 2258, 2380 …) → "(proved)"; 144 mentions of `U-M<n>` in helper docstrings and the `####` section
  comments (`U-M1 helpers (prefix um1_; unit U-M1, 2026-09-15)`, `U-M2: regularity`, …) → drop the unit
  bookkeeping or keep as provenance; 12 mentions of `Statements_FINAL` / `PLAN_FINAL` / `DESIGN_A/B`, which are
  fine as provenance pointers but should cite the file paths;
* the `2026-09-15` dates in the `um1_` and `um4_` section headers.
Statements must stay byte-identical (re-run `check_W1_identity.py` part 2 and the subsequence check of §5 on
the ported module); helper names may be renamed freely (no consumer uses them) — the cross-unit `um*_`
prefixes are a Wave-1 artefact and could become a single `bd_` prefix or `private`.  Registry: none of the
new declarations is a `lean-declarations.json` target or an axiom-policy entry; the four consumer sites
(U_S7G :565, U_R174 :926/:1086, U_R176 :878/:915, U_R177 :1118/:1365) import the module and instantiate
`BigonData` (Wave 2), with the F-176-1 / F-177-1 interface edits of PLAN_FINAL §3.

## 8. Notes

* The unit reports' claims were re-verified on the assembled file (compile, axioms, identity); no unit had
  a false or under-hypothesised sub-leaf, and no fallback (PLAN §6 R1 `j ∈ {1, 2}`) was used — M4 is general `j`.
* The de-duplication removed only proofs whose statements were byte-identical to an earlier helper in the
  same binder context; the assembled file was compiled both before (5567 lines) and after (5470 lines).
* Times: assembled compile ≈ 15 s; the three-file check (assembled + two drafts in parallel) ≈ 20 s.
