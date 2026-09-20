# PORT_REPORT — row 110 thm:C-S7 (+ rows 127 thm:comparison, 128 cor:C-inherits), prepared 2026-09-19 12:48 UTC / 8:48am ET by the W6-GLUE assembler

Source: **`work/drafts/corner/W6_Assembled.lean`** (27,533 lines, sha256 `425724bc9bed22b1…`; W6_ASSEMBLY_REPORT.md), compile
0 errors, 8 `declaration uses sorry` (all DEAD, dropped here); `#print axioms SM.thm_C_S7` there =
`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]`
— the nine registered axioms, NO `sorryAx`.  Nothing was written under `work/lean`; every compile used a scratch object tree
(§4).  Output, all under `work/drafts/corner/port/CS7/`:

| module | lines | sha256 | content | compile (module semantics, `lean -o`) |
|---|---|---|---|---|
| `SM/CS7Units.lean` | 27,164 | `b4993185abca2ad0…` | ALL unit material of the assembled file VERBATIM (waves 3-6: `s7p_ s7r_ s7q_ s7u_ s7g_ s7f_ s7fa_ s7fb_ s7fc_ s7s_ s7sc_ s7sh_ s7k_ s7j_ s7z_ s7o_ w3_ w4_ w5t_ w5s_ w5b_ w5r_ w5_ w6k_ w6c_ w6r_ w6x_ w6_`; 1,431 declarations) minus the 19 dead declarations (§2) and minus the two leaves + the row tail (→ `SM/CS7.lean`); 23 exact-text docstring rewordings (§3); imports `SM.CornerChainUnits SM.CS7Sliding SM.BigonDeletion SM.CarrierFloorRows` (the skeleton's) | **0 errors, 0 warnings, exit 0; 63 s** (91 s in an earlier run under load from two other agents' compiles; not split) |
| `SM/CS7.lean` | 93 | `f2218e30b26c16e8…` | `import SM.CS7Units`; the two branch leaves `s7_sliding_law_at` (body `s7u_sliding_law_at_of hn g h h₁ h₂ (s7u_box_carriers' hn g h h₁ h₂)`, wave 4) and `s7_bigon_law_at` (body `w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)`, the recorded closure line), `thm_C_S7_of`, `thm_C_S7_of_floor`, **`theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor`** (FIXED name `SM.thm_C_S7`, axiom-policy.json) — the tail byte-for-byte from the source; `tools/stmt_check.py --base W3_Skeleton.lean`: **5/5 frozen statements byte-identical, PASS** | 0 errors, 0 warnings, exit 0; 19 s |
| `SM/ComparisonRows.lean` | 22 | `7520de7306ef0dcd…` | imports `SM.CS7 SM.CSoft SM.Comparison SM.CInherits`; `theorem thm_comparison (hR : hyp_R) : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P), cornerStateSum hn hP = amplitude P hP.1 hn := thm_comparison_of hR thm_C_S7 thm_C_soft` and `theorem cor_C_inherits (hR : hyp_R) : CInheritsData := cor_C_inherits_of hR thm_C_S7 thm_C_soft` (FIXED names `SM.thm_comparison`, `SM.cor_C_inherits`; statements as in `work/drafts/comparison/Statements_FINAL.lean` §5 lines 853-860 and `work/drafts/comparison/port/PORT_REPORT.md` §5; the `_of` theorems are `work/lean/SM/Comparison.lean:233`, `work/lean/SM/CInherits.lean:135`) | 0 errors, 0 warnings, exit 0; 24 s |

`grep -c` of `sorry`, `#print`, `#eval`, `#check`, `admit` = **0 in every module** (also in prose).  Header line 1 of every module is the
executor's template with the literal placeholder `<HH:MM>`:
`-- Ported <HH:MM>Z 2026-09-19 from work/drafts/corner/W6_Assembled.lean by the pod executor (files prepared by the W6-GLUE assembler)`.
Four `set_option linter.unusedSectionVars false in` lines (W4_ASSEMBLY_REPORT §8.2, inside FB2's block, cosmetic) remain in
`CS7Units.lean` — disclosed; not in the forbidden list.  Fixed-name check: no `theorem thm_C_S7 / thm_comparison / cor_C_inherits`
exists under `work/lean/{SM,CV,RProof,Bridge}` (only the `_of` forms); `tools/clash_scan.py` on the source: `full_name_clashes: {}`.

## 1. Axioms (scratch object tree, `axioms_port.lean` importing `SM.ComparisonRows`; log `<scratchpad>/w6asmA/compile_port.log`)

| declaration | axioms |
|---|---|
| **`SM.thm_C_S7`**, **`SM.thm_comparison`**, **`SM.cor_C_inherits`** | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]` — the nine registered axioms, no `sorryAx`, no unregistered axiom |
| `SM.s7_bigon_law_at`, `SM.s7_sliding_law_at` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |

(The full census of the source — `#print axioms` on all 1,455 top-level names, `<scratchpad>/w6asmA/allax.log` — shows no
unregistered axiom anywhere and `sorryAx` on exactly the 19 dropped declarations.)

## 2. Deletions (the 19 dead declarations, each with its docstring and `include … in` lines; 291 source lines; `tools/prune.py`)

Every one carries `sorryAx` in the source and lies on no proved path (the census is closed under "used only by dead material":
every consumer of a sorried box is itself sorried).  W3/ROT: `s7q_box_ret` (Prop S1, FALSE as stated on the leg-`M` side, W3_RET_REPORT
§2; superseded by S1P's `s7u_box_ret'`), `s7q_box_rows`, `s7q_exists_contactSector`, `s7q_sliding_law_at_of_boxes` (its consumers),
`w3_SlidingRet_of_box` (shape check).  W3/K: `s7z_F_exists` (B1), `s7z_returned_of_FSector` (B2), `s7z_exists_rowSector` (consumer),
`w3_BigonFSector_of_box`, `w3_BigonReturnedRows_of_box` (shape checks) — superseded by the wave-4 F-aligned route.  W5/BR:
`w5b_box_returnedData` (superseded by `w5_returnedData`), `w5b_box_interlacingTurnData`, `w5b_box_noninterlacingTurnData`,
`w5b_box_curlData` (stated per `t` without a radius / without the wall's radius facts; superseded by `w6_interlacingTurnData`,
`w6_noninterlacingTurnData`, `w6k_box_curlData`), `w5b_interlacingData`, `w5b_noninterlacingData` (BR's wrappers over those boxes;
superseded by `w6_interlacingData` / `w6_noninterlacingData`).  W5/ROW: `w5r_box_branch` (superseded by `w5_box_branch` → `w6_box_branch`).
W5 glue: `w5_branchData`, `w5_box_branch` (superseded by `w6_branchData`, `w6_box_branch`).  Sanity: the pruned source
(`<scratchpad>/w6asmA/W6_Pruned.lean`, 27,242 lines) compiles with 0 errors and 0 warnings.
KEPT although dead (sorry-free W3 scaffolding taking the superseded Props as hypotheses; W4 §7): `w3_SlidingRet`, `w3_box_rows_of`,
`w3_s7_sliding_law_at_of`, `w3_s7_sliding_law_at_of₂`, `w3_BigonFSector`, `w3_BigonReturnedRows`, `w3_s7_bigon_law_at_of`,
`w3_SlidingOrder_of_box`; ROT's `w6r_exists_rotation` (sorry-free, unused by the glue).

## 3. Docstring / prose rewordings (23, exact-text, each asserted unique; `tools/port_build_w6.py` REW)

Prose `sorry` mentions (7): ROT's §S7QBoxes intro ("stated as … black boxes with `sorry`" → "were stated … in wave 3; in wave 4 they are
proved or superseded"), `w3_SlidingOrder`'s two docstrings ("sorry-free" → "complete" / dropped), F's black-box list ("(`sorry`, geometric;
…)" → "(geometric; … PROVED in wave 4 by units FB1, FB2, FB3)"), K's §E heading (→ "B1 and B2 are superseded … (dropped at port); B3 …
is proved"), the `W4Bigon` intro (two sentences: "are sorry-free" → "are proved"; "The leaf keeps its `sorry` (merge rule); it closes as
… once wave 5 lands" → "… (dropped at port).  The leaf closes as … (waves 5-7 prove `w4_box_returnedRows`)").
"BLACK BOX … NOT proved" docstrings of PROVED theorems (16 replacements on 13 theorems): `s7q_box_carriers` ("BLACK BOX (ROT (a)-(c)
geometry …)" → "Prop S3 (…; PROVED in wave 4 through S1P's `s7u_box_carriers'`)"), `s7u_SlidingCarriers'` ("BLACK BOX for unit S3G" →
"DISCHARGED by unit S3G"), `s7f_exists_bigonSplit` / `s7f_exists_twoNewbornTerm` / `s7f_exists_ineligible_transport` ("BLACK BOX n" →
"Box n (…; PROVED by unit FBn)"), `s7s_clear_local` ("BLACK BOX (this unit's own remaining content; NOT proved)" → "Clearance of the local
edges (PROVED by unit SITEC)", its "Estimate 300-450 lines" dropped), `s7s_wallTriangleData_of_bigon` ("BLACK BOX (U110-A/B wall data; NOT
proved here)" → "The wall triangle data at a bigon wall (…; PROVED by unit SITEC)", "Estimate 300-500 lines …" dropped),
`s7z_oneNewborn_exists` ("BLACK BOX — unit J …" → "Prop B3 (PROVED by unit B3) — unit J …"), `w5r_box_transport` (→ "The returned transport
(ROW's Prop, PROVED at the wave-5 assembly from unit RT)", "Nothing below depends on the body" dropped), `w5r_box_corners` (→ "The
contact-corner correspondence (ROW's Prop, PROVED by unit W6-COR)"), `w5r_box_contact` (→ "The contact carrier pair (ROW's Prop, PROVED at
the wave-5 assembly from unit SITE)"), `w6r_box_centreCorners` (→ "The centre corner data below a radius (W6-ROT's consumed Prop, PROVED by
unit W6-CC)"), `w4_box_returnedRows` (→
"Prop B2' (PROVED, waves 5-7: …)", "Nothing below depends on the body" dropped).  Historical references inside unit intros ("BLACK BOX 1,
proved", "serving BLACK BOX 1 `s7f_exists_bigonSplit`") are left as they are.  No statement, name or proof text was changed.

## 4. Collapses (W5_ASSEMBLY_REPORT §7 / W4 §7): NONE applied — the duplicates are kept

`w5r_qH / w5t_qH / w5b_qH`, `w5r_L₁ / w5t_L₁ / w5b_L₁`, `w5r_L₂ / w5t_L₂ / w5b_L₂`, `w5r_x / w5s_x`, `w5r_T₁ / w5t_T₁ / w5b_ι₁`-preimages,
`w5r_sgn_ne_zero / w5_signType_cast_ne_zero`, `w6_signType_neg_neg / w6r_signType_eq_zero_of_neg_eq` (different statements), and W4 §2's
content duplicates (`s7g_CarrierData'` vs S1P's, `s7fa_side_of_r`, `s7fa_sideData`, `s7fa_not_affected_of_ne` vs their B3 twins).  Reason:
each identification is definitional but the names are threaded through hundreds of call sites in five unit blocks whose bodies were
compiled against the duplicated spellings (W5 §3's `erw` workarounds show the spellings are NOT interchangeable under `rw`); a collapse is
a refactor, not a trivial edit.  All are library-internal helpers with unit prefixes; no clash (`full_name_clashes: {}`).

## 5. Compile recipe used (module semantics without touching `work/lean`; `tools/compile_port.sh <portdir>`)

Scratch tree `ptree/O/SM/` = symlinks to the 3,240 files of `work/lean/.lake/build/lib/lean/SM/`; `ptree/T/SM/` = copies of the three
modules; from `work/lean`, `LP=$(lake env printenv LEAN_PATH)`, then in import order
```
LEAN_PATH="ptree/O:$LP" lean --root=ptree/T -o ptree/O/SM/CS7Units.olean      ptree/T/SM/CS7Units.lean      # 63 s, exit 0
LEAN_PATH="ptree/O:$LP" lean --root=ptree/T -o ptree/O/SM/CS7.olean            ptree/T/SM/CS7.lean            # 19 s, exit 0
LEAN_PATH="ptree/O:$LP" lean --root=ptree/T -o ptree/O/SM/ComparisonRows.olean ptree/T/SM/ComparisonRows.lean # 20 s, exit 0
LEAN_PATH="ptree/O:$LP" lean ptree/axioms_port.lean                                                        # §1
```
The log of the run that produced the installed files is `tools/compile_port.log`.  After the executor copies the files to `work/lean/SM/` and fills the header
time, `lake build` (glob `SM.+`) suffices.  Reproduce the port from the source: `python3 tools/prune.py W6_Assembled.lean W6_Pruned.lean
<the 19 names of §2>`, `python3 tools/port_build_w6.py W6_Pruned.lean <outdir> [--time HH:MM]`, `tools/compile_port.sh <outdir>` (paths
inside the scripts point at the assembler's scratch directory `<scratchpad>/w6asmA/`; adjust `S=`).

## 6. Row mapping for `work/lean/lean-declarations.json` (executor)

`thm:C-S7` → `SM.thm_C_S7` (module `SM.CS7`), `thm:comparison` → `SM.thm_comparison`, `cor:C-inherits` → `SM.cor_C_inherits` (module
`SM.ComparisonRows`); all three `pending` with the fixed names already recorded (axiom-policy.json:41-48).  The CV/R tail's
`corner_laws_and_soft` reads `cor_C_inherits Bridge.sm_R` (comparison PORT_REPORT §8) — unchanged by this port.
