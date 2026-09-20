# PORT_REPORT — row 110 thm:C-S7 (and rows 127/128), port files prepared by the W6-GLUE assembler (assembly B), 2026-09-19 12:52 UTC / 8:52am ET

Source: **`work/drafts/corner/W6_Assembled_B.lean`** (27,531 lines, sha256 `3726574202bb1b676a9b637f7213abfad113373bcdf4be9442cd4cf233661ae2`; `W6_ASSEMBLY_REPORT_B.md`), the wave-6 merge in
which `SM.thm_C_S7` is sorry-free on the nine registered axioms.  Nothing was written under `work/lean`; `lake build` was not run; every
compile used the scratch `.olean` recipe of `work/drafts/cvtail/port/PORT_REPORT.md` §8.5 (`tools/port_compile_B.sh`: copy the modules to
`T/SM/`, symlink every accepted `SM` `.olean`/`.ilean` into `O/SM/`, `lean --root=T -o O/SM/X.olean` in import order with `O` first on
`LEAN_PATH`, then the scratch importer `Axioms.lean` — the `#print axioms` probe lives ONLY there).  Output, all under
`work/drafts/corner/port/CS7_B/`:

| module | lines | sha256 (prefix) | content | compile (`lean --root -o`, scratch tree) |
|---|---|---|---|---|
| `SM/CS7Units.lean` | 27,000 | `3fc85648cff533f1…` | the unit corpus: every declaration of the assembled file from `namespace SM` (line 17) to `end VertexEdge` (27491) except the two leaves and the 26 deletions of §2 (468 lines), with the 27 rewordings of §3; imports `SM.CornerChainUnits SM.CS7Sliding SM.BigonDeletion SM.CarrierFloorRows` (the assembled file's) | 0 errors, 0 warnings, 72 s (60 s in the first scratch run; 105 s when a full-file compile ran concurrently) |
| `SM/CS7.lean` | 97 | `62ed7f39730b1e18…` | the frozen declarations of `W3_Skeleton.lean`: `s7_sliding_law_at` (assembled 8490-8501), `s7_bigon_law_at` (27476-27488, body = the recorded closure line), `end VertexEdge` … `thm_C_S7_of`, `thm_C_S7_of_floor`, `theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor` (27491-27531), all VERBATIM; imports `SM.CS7Units SM.CarrierFloorRows`; wrappers `namespace SM` / `open Link Carrier` / `attribute [local instance] Classical.propDecidable` / `noncomputable section` / `section VertexEdge` / `variable {n : ℕ} [NeZero n]` repeated | 0 errors, 0 warnings, 23 s |
| `SM/ComparisonRows.lean` | 26 | `0f183c84e69d61f9…` | rows 127/128 (FIXED names `SM.thm_comparison`, `SM.cor_C_inherits`): signatures verbatim from `work/drafts/comparison/Comparison_Assembled.lean` 1009-1011 and 1016 (the placeholder bodies' trailing ` by` dropped), bodies `thm_comparison_of hR thm_C_S7 thm_C_soft` / `cor_C_inherits_of hR thm_C_S7 thm_C_soft` (the one-liners of `work/drafts/comparison/port/PORT_REPORT.md` §5); imports `SM.CS7 SM.CSoft SM.Comparison SM.CInherits` | 0 errors, 0 warnings, 25 s |

`CS7Units.lean` compiles in 72 s (60 s in the first scratch run; 105 s when a full-file compile ran concurrently) (`-o`), under the ~90 s threshold, so it is ONE module; `tools/port_build_B.py --split 8503`
produces `CS7UnitsA.lean` (sliding branch, through S1P) / `CS7UnitsB.lean` (bigon branch, from unit F) at the unit-F module docstring if
the executor prefers two modules (not exercised).  Frozen statements: `python3 ../../tools/stmt_check.py SM/CS7.lean --base ../../W3_Skeleton.lean`
→ 5/5 byte-identical and unique (PASS).  Forbidden strings: none of `sorry`, `sorried`, `sorryAx`, `#print`, `#eval`, `#check`, `#reduce`,
`admit`, line-initial `axiom` in any of the three files, prose included (checked by the builder, `grep -c -i sorr` = 0 each); the units keep
four `set_option linter.unusedSectionVars false in` lines (nine accepted `SM/*.lean` files carry `set_option`).  Header line 1 of every
module: `-- Ported <HH:MM>Z 2026-09-19 from work/drafts/corner/W6_Assembled_B.lean by the pod executor (files prepared by the W6-GLUE
assembler): …` with the literal placeholder `<HH:MM>`.  Module names `CS7Units`, `CS7`, `ComparisonRows` do not exist under `work/lean/SM/`;
the assembled file's clash scan against every `.lean` under `work/lean` reports `full_name_clashes: {}` for all 1,448 new declarations
(the port declares a subset of them plus the three fixed row names, which exist nowhere yet).

## 1. Axioms (scratch tree, `Axioms.lean` importing `SM.ComparisonRows`)

| declaration | axioms |
|---|---|
| **`SM.thm_C_S7`** | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]` |
| **`SM.thm_comparison`**, **`SM.cor_C_inherits`**, `SM.thm_C_soft` | the same nine |
| `SM.thm_C_S7_of_floor`, `SM.thm_C_S7_of`, `SM.s7_bigon_law_at`, `SM.s7_sliding_law_at`, `SM.w4_box_returnedRows` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |

No `sorryAx`, no unregistered axiom.

## 2. Deletions (26 declarations, 468 lines with their docstrings and `include … in` lines; `tools/deletions.json`)

All are draft material on no path to any frozen declaration (whole-file `#print axioms` of the assembled file: `sorryAx` occurs in exactly
the first 19; the last 7 are sorry-free but exist only for them — W4_ASSEMBLY_REPORT §7's list).  The builder's reference scan finds no
code reference to a deleted name in the kept text.

| # | declaration (SM.) | kind | reason |
|---|---|---|---|
| 1 | `s7q_box_ret` | own `sorry` | W3/ROT's Prop S1, FALSE as stated on the leg-`M` side (W3_RET_REPORT §2); superseded by S1P's `s7u_box_ret'` |
| 2-4 | `s7q_box_rows`, `s7q_exists_contactSector`, `s7q_sliding_law_at_of_boxes` | inherit `sorryAx` from 1 | ROT's route through S1 |
| 5 | `w3_SlidingRet_of_box` | inherits from 1 | W3 shape check of S1 |
| 6 | `w3_SlidingRet` | sorry-free `def` | the Prop S1 itself (false as stated) |
| 7-9 | `w3_box_rows_of`, `w3_s7_sliding_law_at_of`, `w3_s7_sliding_law_at_of₂` | sorry-free | take `hret : w3_SlidingRet`; superseded by `s7u_sliding_law_at_of` (S1P) |
| 10-11 | `s7z_F_exists`, `s7z_returned_of_FSector` | own `sorry` | K's boxes B1, B2; superseded by the F-aligned route (W4) |
| 12 | `s7z_exists_rowSector` | inherits from 10-11 | K's row-sector existence |
| 13-14 | `w3_BigonFSector_of_box`, `w3_BigonReturnedRows_of_box` | inherit from 10-11 | W3 shape checks of B1, B2 |
| 15-16 | `w3_BigonFSector`, `w3_BigonReturnedRows` | sorry-free `def`s | K's Props B1, B2 |
| 17 | `w3_s7_bigon_law_at_of` | sorry-free | takes B1, B2; superseded by `w4_s7_bigon_law_at_of` |
| 18 | `w5b_box_returnedData` | own `sorry` | BR's returned-transport box; discharged in the shape `w5_returnedData` (W5) |
| 19-20 | `w5b_box_interlacingTurnData`, `w5b_box_noninterlacingTurnData` | own `sorry` | BR's turn boxes, stated for every `t` without a radius; superseded by `w6_interlacingTurnData` / `w6_noninterlacingTurnData` |
| 21 | `w5b_box_curlData` | own `sorry` | BR's curl box, not derivable from `hloc ht` alone (W6_CURL_REPORT §2); superseded by `w6k_box_curlData` |
| 22-23 | `w5b_interlacingData`, `w5b_noninterlacingData` | inherit from 19-20 | BR's deliverables; superseded by `w6_interlacingData` / `w6_noninterlacingData` |
| 24-25 | `w5_branchData`, `w5_box_branch` | inherit from 19-21 | wave-5 glue; superseded by `w6_branchData` / `w6_box_branch` |
| 26 | `w5r_box_branch` | own `sorry` | ROW's branch box without the selector hypothesis; superseded by `w6_box_branch` |

## 3. Docstring rewordings (27; `tools/reword.json`, each applied exactly once by the builder; statements, names and bodies untouched)

Prose `sorry` / `sorried` / `sorryAx` mentions (15): ROT's module docstring (`s7q_` boxes "with `sorry`" → discharged/superseded), the two
W3Sliding S2 remarks ("sorry-free" → "complete" / "no placeholder"), unit F's "**Black boxes** (`sorry`, …)" (→ all three PROVED in wave 4 by
FB1, FB2, FB3), K's module docstring remark on `s7z_exists_rowSector` and its heading E (→ B1/B2 superseded and dropped, B3 PROVED), the
W4Bigon glue docstring (three sentences: "sorry-free" → "fully proved"; "stay sorried … keeps its `sorry` … once wave 5 lands" → superseded /
CLOSED by the recorded line), `w4_s7_bigon_law_at_of`'s "closes as … once wave 5 lands" (→ closed, wave 6), ROW's "each `w5r_box_*` is a sorried
theorem" (→ black-box theorem; which are discharged / superseded), the W5Glue docstring (two bullets: `w5b_box_returnedData` "stays sorried"
→ unproved and UNUSED, dropped; the `w5_branchData` / `w5_box_branch` bullet marked superseded by the wave-6 glue; `w5r_box_branch` "stays sorried"
→ "stays unproved"), BR's Part-6 docstring (one sentence added: the per-`t` boxes and their two consumers dropped in favour of the wave-6 glue).
`**BLACK BOX …**` heads of the twelve now-proved theorems (12): `s7q_box_carriers`, `s7f_exists_bigonSplit` (FB1), `s7f_exists_twoNewbornTerm`
(FB2), `s7f_exists_ineligible_transport` (FB3), `s7s_clear_local` (SITEC), `s7s_wallTriangleData_of_bigon` (SITEH), `s7z_oneNewborn_exists` (B3),
`w5r_box_transport` (W5 merge, `w5_transportData`), `w5r_box_corners` (W6-COR), `w5r_box_contact` (W5 merge, `w5_contactData`),
`w6r_box_centreCorners` (W6-CC), `w4_box_returnedRows` (W5/W6 merges) → `**PROVED (…; formerly BLACK BOX …)**`.  References to "BLACK BOX 2"
inside other docstrings (e.g. `s7f_triangle_data`) and the `def` `s7u_SlidingCarriers'` ("BLACK BOX for unit S3G") are left as they are
(they are not claims that a theorem is unproved).

## 4. Collapses: none applied (kept duplicates, to be collapsed later if desired)

`w5r_qH / w5t_qH / w5b_qH`, `w5r_L₁ / w5t_L₁ / w5b_L₁`, `w5r_L₂ / w5t_L₂ / w5b_L₂`, `w5r_x / w5s_x`, `w5r_T₁ / w5t_T₁ / w5b_ι₁`-preimages,
`w5r_sgn_ne_zero / w5_signType_cast_ne_zero`, and W4 §2's content duplicates (`s7g_CarrierData'` vs S1P's, `s7fa_side_of_r`, `s7fa_sideData`,
`s7fa_not_affected_of_ne` vs their B3 twins).  Not trivial: they are `def`s used across thousands of lines whose unit proofs rely on
`exact`-level unfolding between the spellings (W5 §3); a collapse is a separate, compile-verified refactor.

## 5. Installation (executor)

`cp port/CS7_B/SM/{CS7Units,CS7,ComparisonRows}.lean work/lean/SM/`; replace `<HH:MM>` in line 1 of each; `lake build` (the `SM.+` glob of the
lakefile picks them up); `tools/check_lean.py` for the fixed names `SM.thm_C_S7`, `SM.thm_comparison`, `SM.cor_C_inherits`
(`work/lean/axiom-policy.json` targets `thm:C-S7`, `thm:comparison`, `cor:C-inherits`).  Rebuild with `tools/port_build_B.py --src
work/drafts/corner/W6_Assembled_B.lean --del tools/deletions.json --reword tools/reword.json --out port/CS7_B [--time HH:MM] [--split 8503]`.
