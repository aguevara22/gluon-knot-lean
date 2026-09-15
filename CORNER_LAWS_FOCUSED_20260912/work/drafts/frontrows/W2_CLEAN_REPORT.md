# W2_CLEAN_REPORT — front certificate rows, wave-2 clean subset (rows 81 ng:circle, 82 ng:cusp-skein)

2026-09-14 12:35 UTC / 8:35am ET.  Input: `work/drafts/frontrows/Skeleton_W2.lean` (14,891 lines, 5 open leaves; MERGE2_REPORT.md).
Output: **`work/drafts/frontrows/FrontRows_W2_Clean.lean`** (14,665 lines), produced by
`work/drafts/frontrows/clean_w2.py` (rerunnable; it deletes the Skeleton_W2 line ranges of §3 below, asserts the first line
of every range, and rewrites the module header and the L-geo section note).  Intended destination once accepted:
`work/lean/SM/FrontRowsW2.lean` (module `SM.FrontRowsW2`; nothing was written under `work/lean` — the module has the same
imports as Skeleton_W2 and was compiled in place with `cd work/lean && lake env lean ../drafts/frontrows/FrontRows_W2_Clean.lean`).

## 1. Result

| item | value |
|---|---|
| file | `work/drafts/frontrows/FrontRows_W2_Clean.lean`, 14,665 lines (Skeleton_W2: 14,891; 240 lines deleted, header rewritten) |
| `grep -c -i sorry` | **0** (Skeleton_W2: 5) — no occurrence in code or docstrings |
| `#print` / `#eval` / `#check` / `set_option` lines | none |
| compile | **0 errors**, exit 0, 42 s wall (log `/tmp/w2clean/compile_clean.log`, final recompile `/tmp/w2clean/compile_clean_final.log`) |
| warnings | the 4 pre-existing U8R linter warnings only (unused section variables in `U8R.lexKey_injective` L13370 and `U8R.mem_fib` L13391; unreferenced binders `q` L14056:46, `t` L14175:53), all already in `W2_U8R.lean` / MERGE2_REPORT §1.  **No** `declaration uses sorry` warning |
| axioms (probe copy `/tmp/w2clean/W2_ax.lean` = module + `#print axioms`, log `/tmp/w2clean/compile_ax.log`) | `SM.ng_circle`, `SM.ng_cusp_skein`, `SM.ng_cusp_skein_both`: **`[propext, Classical.choice, Quot.sound, SM.lp_lm]`** (as expected; `lp_lm` is the accepted literature interface reached through `P`).  Also checked: `SM.FrontRows.base_defect_nonneg`, `deform_P`, `P_comm`, `P_zigzag`, `PLFront.IsStandardCircles.defect_eq_zero` — the same four axioms, no `sorryAx` |
| name clashes against `work/lean` | **none** (§4) |
| top-level declarations in the module | 1,116 (all distinct fully-qualified names; list of all: `python3 work/drafts/frontrows/clash_scan_w2.py` writes `/tmp/w2clean/clean_decls.txt`) |

## 2. Method

1. Copied Skeleton_W2.lean.
2. Deleted the five open leaves (`typeIII_site`, `typeII_move`, `typeI_move`, `crossedCusp_move`, `represent`) with their docstrings,
   then every declaration whose statement or body refers to a deleted declaration, transitively.  The dependency closure was
   determined by a reference scan (`grep -n -w` over the skeleton for each deleted name) and confirmed by the compile: the four
   polynomial consumers `P_typeIII/P_typeII/P_typeI/P_crossedCusp` (each uses one leaf), the five rows 76-80 (`ng_commutation`
   uses `represent`; 77-79 use a `P_type*`; `ng_deletions` uses `P_crossedCusp`), `certificate_laws` (uses rows 76-80),
   `word_bound` (uses `certificate_laws`), `ng_local_front_bound` (uses `ng_commutation.represent` and `word_bound`).
   Nothing inside the unit blocks refers to a leaf: the four L-geo leaves sit AFTER `end U4` and `represent` sits AFTER
   `end U8RInfra` in the skeleton, so U2/U3/U4/U7/U8D/U8R are untouched.  The only other declarations mentioning the deleted names are
   docstrings (prose references to `typeIII_site` etc. at clean L1139, L8726, L10934, L13336, L13819, L13881, L13889), kept.
3. Deleted also the six row-statement structures `NgCommutationClauses`, `NgFrontIClauses`, `NgFrontIIClauses`, `NgFrontIIIClauses`,
   `NgDeletionsClauses`, `NgLocalFrontBoundClauses` (the statements of the removed rows; not needed by `ng_circle`/`ng_cusp_skein`;
   nothing else refers to them).  Kept `SmoothFront.NonsingularDeformation` (used by `deform_downCount/writhe/P` and by U8D),
   `NgCircleClauses`, `NgCuspSkeinClauses`, and every definition, structure and theorem that does not depend on a deleted item —
   in particular the whole U1 count layer, the record core U2, the record rows U3, the geometry core U4 (infrastructure for the
   removed L-geo leaves), the U7 planarity helpers, U8D, and the U8R infrastructure (infrastructure for the removed `represent`).
4. Header rewritten (module described as the wave-2 clean subset of the lane: rows 81 and 82 and the shared infrastructure, with
   the list of what is not in the module); the L-geo section docstring (skeleton L11085-11091) replaced by a 3-line note; the
   "Statements" section docstring (clean L57) reworded.  No other text changed; the word "sorry" appears nowhere.

## 3. Removed declarations (Skeleton_W2.lean line ranges, inclusive; each range includes the docstring and the trailing blank line)

The delta module (`import SM.FrontRowsW2`, then `namespace SM`, `open SM.FrontWord SM.Link`, `open scoped ContDiff`) must
re-declare exactly these, in this order (statements verbatim from the skeleton; the five leaves with real proofs):

| # | declaration (full name) | kind | Skeleton_W2 lines | depends on (removed) | where it goes in the delta module |
|---|---|---|---|---|---|
| 1 | `SM.NgCommutationClauses` | structure | 57-73 (decl 57-72) | — (statement only; mentions `SmoothFront.NonsingularDeformation`, kept) | `namespace SM` |
| 2 | `SM.NgFrontIClauses` | structure | 74-76 (decl 74-75) | — | `namespace SM` |
| 3 | `SM.NgFrontIIClauses` | structure | 77-84 (decl 77-83) | — | `namespace SM` |
| 4 | `SM.NgFrontIIIClauses` | structure | 85-92 (decl 85-91) | — | `namespace SM` |
| 5 | `SM.NgDeletionsClauses` | structure | 93-102 (decl 93-101) | — | `namespace SM` |
| 6 | `SM.NgLocalFrontBoundClauses` | structure | 119-122 (decl 119-121) | — | `namespace SM` |
| — | L-geo section docstring | `/-! ### L-geo … -/` | 11085-11092 | (prose; replaced by a note in the clean module) | — |
| 7 | `SM.FrontRows.typeIII_site` | theorem (OPEN leaf, U5) | 11093-11102 (decl 11100-11101) | — | `namespace FrontRows` (needs `open SM.FrontRealize …` as U5 chooses) |
| 8 | `SM.FrontRows.typeII_move` | theorem (OPEN leaf, U6) | 11103-11112 (decl 11109-11111) | — | `namespace FrontRows` |
| 9 | `SM.FrontRows.typeI_move` | theorem (OPEN leaf, U6) | 11113-11120 (decl 11117-11119) | — | `namespace FrontRows` |
| 10 | `SM.FrontRows.crossedCusp_move` | theorem (OPEN leaf, U6) | 11121-11129 (decl 11126-11128) | — | `namespace FrontRows` |
| 11 | `SM.FrontRows.represent` | theorem (OPEN leaf, U8R) | 14568-14574 (decl 14571-14573) | — (reduce via the kept `U8R.represent_of_sweepStatement`) | `namespace FrontRows` |
| 12 | `SM.FrontRows.P_typeIII` | theorem | 14619-14623 | 7 | `namespace FrontRows` |
| 13 | `SM.FrontRows.P_typeII` | theorem | 14625-14629 | 8 | `namespace FrontRows` |
| 14 | `SM.FrontRows.P_typeI` | theorem | 14631-14635 | 9 | `namespace FrontRows` |
| 15 | `SM.FrontRows.P_crossedCusp` | theorem | 14637-14643 (decl 14637-14641; 14642-14643 blank) | 10 | `namespace FrontRows` |
| 16 | `SM.ng_commutation` (row 76) | theorem | 14741-14756 (decl 14741-14755) | 1, 11 (+ kept `comm_counts`, `P_comm`, `deform_*`) | after `end FrontRows`, `open FrontRows` |
| 17 | `SM.ng_front_I` (row 77) | theorem | 14757-14764 (decl 14757-14763) | 2, 14 (+ kept `typeI_counts`) | idem |
| 18 | `SM.ng_front_II` (row 78) | theorem | 14765-14773 (decl 14765-14772) | 3, 13 (+ kept `typeII_counts`) | idem |
| 19 | `SM.ng_front_III` (row 79) | theorem | 14774-14782 (decl 14774-14781) | 4, 12 (+ kept `typeIII_counts`) | idem |
| 20 | `SM.ng_deletions` (row 80) | theorem | 14783-14804 (decl 14783-14803) | 5, 15 (+ kept `zigzag_counts`, `P_zigzag`, `crossedCusp_counts`, `IsZigzagDeletion.source_ne_nil`, `IsCrossedCuspShortcut.ne_nil`) | idem |
| — | `namespace FrontRows` + `/-! ## Row 83 … -/` | wrapper | 14842-14845 | — | — |
| 21 | `SM.FrontRows.certificate_laws` | theorem | 14846-14868 (decl 14850-14867) | 16-20 (+ kept `ng_circle`, `ng_cusp_skein`, `base_defect_nonneg`; accepted `wordMoves_pres_s/del_s/skein_s`) | `namespace FrontRows` (second block) |
| 22 | `SM.FrontRows.word_bound` | theorem | 14869-14875 (decl 14873-14874) | 21 (+ accepted `ng_finite_word_bound`) | idem |
| — | `end FrontRows` | wrapper | 14876-14877 | — | — |
| 23 | `SM.ng_local_front_bound` (row 83) | theorem | 14878-14890 (decl 14878-14889) | 6, 16, 22 (+ accepted `presentations`, `SmoothFront.defect_nonneg_iff`) | after `end FrontRows` |
| — | old module header | `/-! # … -/` | 15-40 | replaced (new header L15-50 of the clean module) | — |

Total deleted: 16 ranges, 240 lines; 23 named declarations (6 structures, 5 open leaves, 4 polynomial consumers, 6 rows, `certificate_laws`, `word_bound`).
Nothing else was removed; in particular ALL of the following stay in the clean module and must NOT be re-declared by the delta:
`comm_counts`, `typeI_counts`, `typeII_counts`, `typeIII_counts`, `zigzag_counts`, `crossedCusp_counts`, `circleDeletion_counts`,
`skein_counts`; `comm_recordIso`, `zigzag_recordIso`, `circle_recordIso_addFree`, `SkeinSite`, `skein_site`, `skein_unique`;
`PLFront.IsStandardCircles.downCount_eq_c_general`; `deform_downCount`, `deform_writhe`, `deform_P`; `degAZ_delta_pow`,
`switch_of_recursion_pos/neg`, `P_comm`, `P_zigzag`, `P_circleDeletion`, `PLFront.IsStandardCircles.defect_eq_zero`,
`base_defect_nonneg`, `skein_ineq_forward/backward`; the namespaces `SM.FrontRows.U2/U3/U4/U8D/U8R` and the sections
`U1Infra`, `u7_helpers` in full.

## 4. Name-clash scan (namespace-aware)

`work/drafts/frontrows/clash_scan_w2.py`: builds the fully-qualified name (tracking `namespace`/`section`/`end`, skipping
comments) of every top-level `theorem/lemma/def/abbrev/structure/inductive/class/instance/opaque/axiom` in the clean module
(1,116 declarations, 1,116 distinct names) and in every `.lean` under `work/lean` outside `.lake` (658 files), and intersects.
**Result: 0 clashes.**  Namespaces used by the clean module: `SM` (5: `NgCircleClauses`, `NgCuspSkeinClauses`, `ng_circle`,
`ng_cusp_skein`, `ng_cusp_skein_both`), `SM.SmoothFront` (1: `NonsingularDeformation`), `SM.FrontWord.Is*` (4 nonemptiness helpers),
`SM.FrontRows` (106) and `SM.FrontRows.U2` (156), `.U3` (331), `.U4` (138 + sub-namespaces `HalfPlane`, `MatchData`, `Chain`,
`Chain.IsChain`, `SegIn`, `SegOut`, `SigmaMeet`, `MeetSpec`), `.U8D` (102 + `OccHyp`, `CuspHyp`, `Sep`, `FrontRecEquiv`), `.U8R` (128),
`SM.FrontRows.PLFront.IsStandardCircles` (2).  Secondary short-name check (any namespace) for the row-level names `ng_circle`,
`ng_cusp_skein`, `ng_cusp_skein_both`, `NgCircleClauses`, `NgCuspSkeinClauses`, `NonsingularDeformation`, `SkeinSite`, `skein_site`,
`skein_unique`, `base_defect_nonneg`, `P_circleDeletion`, `P_comm`, `P_zigzag`, `delta_ne_zero`, `degAZ_delta(_pow)`,
`skein_ineq_forward/backward`, `comm_counts`, `skein_counts`, `deform_P`, `defect_eq_zero`, `downCount_eq_c_general`: no
declaration of any of them in `work/lean`; the only short-name coincidence is `source_ne_nil`, which exists as
`SM.Pres.source_ne_nil` (`SM/FrontRealizeCorrespondence.lean:974`) versus ours `SM.FrontWord.IsZigzagDeletion.source_ne_nil` —
different namespaces, no clash (the skeleton already compiled with both in scope).

## 5. Statement declarations of rows 81 and 82 in the clean module (FrontRows_W2_Clean.lean line numbers)

| declaration | kind | clean line | notes |
|---|---|---|---|
| `SM.SmoothFront.NonsingularDeformation` | structure | 59-65 | kept (used by `deform_*`, U8D) |
| **`SM.NgCircleClauses`** | structure (row 81 statement) | 67-71 | fields `circleDeletion_B`, `single_B`, `union_B` |
| **`SM.NgCuspSkeinClauses`** | structure (row 82 statement) | 73-81 | fields `earlier_branch`, `unique_smoothing`, `smoothing_s`, `principal_s` |
| **`SM.ng_circle`** | theorem `: NgCircleClauses` | 14631-14641 | uses `circleDeletion_counts` (1086), `P_circleDeletion` (14527), `delta_ne_zero` (131), `degAZ_delta` (156), `PLFront.IsStandardCircles.defect_eq_zero` (14535) |
| **`SM.ng_cusp_skein`** | theorem `: NgCuspSkeinClauses` | 14643-14657 | uses `skein_ineq_forward` (14555), `skein_ineq_backward` (14589), `skein_unique` (8709), `IsCuspSkein.ne_nil` (99) |
| **`SM.ng_cusp_skein_both`** | theorem | 14660-14663 | from `ng_cusp_skein.earlier_branch` |

Block map of the clean module: header L15-50; `namespace SM` L52; statements L57-81; `namespace FrontWord` helpers L85-104;
`namespace FrontRows` L106; `section Leaves` L110-14487 (L-deg L112-201; L-cnt L202-1126 (`section U1Infra` L211-902, the count leaves L904-1124);
`namespace U2` L1141-2879; `namespace U3` L2891-8565; L-rec L8568-8715 (leaves L8577-8714); `namespace U4` L8728-11043; L-geo note L11045-11047;
`section u7_helpers` L11051-11690; `PLFront.IsStandardCircles.downCount_eq_c_general` L11696; `namespace U8D` L11708-13316;
`deform_downCount/writhe/P` L13322-13334; `section U8RInfra`/`namespace U8R` L13350-14485); glue L14489-14621
(`degAZ_delta_pow` 14494, `switch_of_recursion_pos/neg` 14503/14509, `P_comm` 14517, `P_zigzag` 14522, `P_circleDeletion` 14527,
`defect_eq_zero` 14535, `base_defect_nonneg` 14543, `skein_ineq_forward` 14555, `skein_ineq_backward` 14589); `end FrontRows` L14622;
`open FrontRows` L14624; rows L14631-14663; `end SM` L14665.

## 6. Files

- `work/drafts/frontrows/FrontRows_W2_Clean.lean` — the module (14,665 lines).
- `work/drafts/frontrows/clean_w2.py` — regenerates it from Skeleton_W2.lean (asserts every deleted range).
- `work/drafts/frontrows/clash_scan_w2.py` — the namespace-aware clash scan (§4).
- `/tmp/w2clean/` — compile logs (`compile_clean.log`, `compile_clean_final.log`, `compile_ax.log`), the axiom probe `W2_ax.lean`, `clean_decls.txt` (ephemeral).
