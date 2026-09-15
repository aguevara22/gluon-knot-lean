# MERGE3_REPORT — front certificate rows, wave 3a merge (U5 + U6: the four L-geo leaves)

2026-09-14 17:25 UTC / 1:25pm ET, merger for the frontrows lane, wave 3a.  Inputs: `Skeleton_W2.lean` (14,891 lines,
5 sorries) and the two unit files `W3_U5.lean` (16,855 lines, W3_U5_REPORT.md) and `W3_U6.lean` (29,216 lines,
W3_U6_REPORT.md).  Output: **`work/drafts/frontrows/Skeleton_W3.lean`** (31,181 lines), produced by the script
**`work/drafts/frontrows/merge3.py`** (rerunnable; it re-derives every hunk from `diff Skeleton_W2.lean W3_Ux.lean`,
refuses deletion hunks, more than one inserted block per unit, a changed statement prefix, an unbalanced block or a
`sorry` inside a block, checks the units' hunks for overlap, applies bottom-up and verifies every hunk verbatim and
contiguous in the output).  Compiled only with `cd work/lean && lake env lean ../drafts/frontrows/Skeleton_W3.lean`;
nothing under `work/lean` was touched; no `lake build`.  Scratch: `/tmp/lean_merge3/` (axiom probes `W3_ax.lean`,
`W3_ax2.lean`, the declaration list `w3a_new_decls.txt`), logs `/workspace/scratch/merge3_compile.log`,
`merge3_axioms.log`, `merge3_axioms2.log`.

## 1. Result

| item | value |
|---|---|
| file | `work/drafts/frontrows/Skeleton_W3.lean`, **31,181 lines** (W2: 14,891; +1,950 U5 block, +14,325 U6 block, +14 lines of the `typeIII_site` body, +1 blank per block) |
| `grep -c sorry` | **1** (W2: 5; U5 closed `typeIII_site`, U6 closed `typeII_move`, `typeI_move`, `crossedCusp_move`).  The one left is **`represent`** (L30860-30862, unit U8R) — handled by the separate sweep lane, NOT touched here (§4) |
| compile (`cd work/lean && lake env lean ../drafts/frontrows/Skeleton_W3.lean`) | **0 errors, exit 0**, 114 s wall (log `/workspace/scratch/merge3_compile.log`) |
| warnings | 59 (the log has 69 lines containing `warning:`; 10 are the `Hint: …` continuation lines of the "Variable name … not explicitly referenced" warnings).  **1** × `declaration uses sorry` (`represent`, L30860); 36 × "Unused tactic linter: `omega` does nothing"; 8 × "this tactic is never executed"; 10 × "Variable name `c`/`c'`/`q`/`t` is not explicitly referenced"; 2 × "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"; 2 × "automatically included section variable(s) unused" (U8R `lexKey_injective` L29740, `mem_fib` L29761).  **Exactly the warning set of `W3_U6.lean`'s own compile** (`/tmp/u6/full3.log`, 60 warnings) shifted by +1,964 lines (the U5 insertion), minus the `typeIII_site` sorry-warning that U5 removed — checked programmatically (set equality).  By region: 32 in the U6 block's (a)/(c)/type-I/crossed-cusp part, 22 in its (b)/(d) tail, 4 in the W2 U8R block, 1 the `represent` leaf.  The U5 block compiles with zero warnings.  **Nothing new from the merge** |
| remaining leaf | `represent` (L30860), U8R — the sweep lane (§4) |
| rows sorry-free (`#print axioms`, §5) | **77 `SM.ng_front_I`, 78 `SM.ng_front_II`, 79 `SM.ng_front_III`, 80 `SM.ng_deletions`** (new this wave) and **81 `SM.ng_circle`, 82 `SM.ng_cusp_skein`** (since wave 2): all `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`lp_lm` = the accepted literature interface reached through `P`).  Rows 76 `ng_commutation` and 83 `ng_local_front_bound` still reach `sorryAx`, now **only** through `represent` |
| the four L-geo leaves | `typeIII_site`, `typeII_move`, `typeI_move`, `crossedCusp_move`: `[propext, Classical.choice, Quot.sound]`; `P_typeI/II/III`, `P_crossedCusp`: `+ SM.lp_lm` — no `sorryAx` |
| clashes / renames | **none needed**: no fully-qualified name of the new blocks is declared by any module of `work/lean` other than `SM/FrontRowsW3.lean`, which is the **byte-identical port of these same blocks** (delta module, ported 17:10Z today, §6); U5 ∩ U6 = ∅, new blocks ∩ rest of the skeleton = ∅ (§6) |

## 2. Verification of the units (task step 1)

`diff Skeleton_W2.lean W3_Ux.lean` for each unit, hunk by hunk (W2 line numbers; `merge3.py` performs the same checks and aborts on a violation):

| unit | hunks | kind |
|---|---|---|
| U5 | `11092a11093,13042` (+1,950 lines: `/-! ### U5 infrastructure -/` … `namespace U5` … `end` … `end U5`, blank); `11101c13051,13065` | ONE insertion (right after the L-geo section docstring, before the `typeIII_site` docstring) + the leaf body `typeIII_site` (`:= sorry` → `:= by` + 14 lines) |
| U6 | `11102a11103,25427` (+14,325 lines: `/-! ### U6 infrastructure -/`, unit docstring, `namespace U6` … `end` … `end U6`, blank); `11111c25436`, `11119c25444`, `11128c25453` | ONE insertion (right after `typeIII_site`, before the `typeII_move` docstring) + the three leaf bodies `typeII_move := U6.typeII_move_proof h`, `typeI_move := U6.typeI_move_proof h`, `crossedCusp_move := U6.crossedCusp_move_proof h` |

Checks performed:
- **No deletion hunk** in either unit (only `a` and `c`); the only W2 lines absent from a unit file are that unit's own leaf `sorry` lines (1 for U5, 3 for U6).
- **Every `c` hunk replaces exactly one line ending `:= sorry`**, and the replacement's first line is *identical up to `:=`*
  (statement, name, binders, docstring untouched — the docstring lines are outside the hunk); no `sorry` in any new body.
  Verified programmatically for all 4 `c` hunks (`statement-prefix identical=True`).
- **Scoping.** Each inserted block is closed: `namespace U5` / `open SM.FrontRealize SM.FrontWord.Letter Equiv U4` /
  `noncomputable section` … `end` / `end U5`; `namespace U6` / `open SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4` /
  `noncomputable section` … `end` / `end U6`.  Stack-tracking scan: nesting balanced, no `set_option`, no `attribute`, no
  `import`, no top-level directive outside the block's namespace; the 30 `open U3` and 116 `local notation` lines of U6 are
  section-local.  The U6 block declares **11 tactic macros** without `local`/`scoped` (`cc_mem` L14146, `ccr_mem` L15246,
  `tI_mem` L16458, `tI_pair` L16809, `tU_pair` L18267, `tIIL_mem` L19447, `tIIR_mem` L19453, `aII_pair` L20467,
  `cII_pair` L22455, and — new in this final U6 — `bII_pair` L24369, `dII_pair` L26305); they are global syntax
  extensions and are kept verbatim (§6, §7).  The U5 block declares no syntax.
- **Non-overlap.** Insertion points 11092 (U5) and 11102 (U6); replaced lines 11101 (U5) and 11111, 11119, 11128 (U6) —
  disjoint, so the merge is order-independent (`merge3.py`: "no overlapping hunks").
- **Containment (after the merge).** Every unit hunk occurs verbatim and contiguously in `Skeleton_W3.lean`
  (`merge3.py` verify pass); the residual of the base is exactly the 4 replaced leaf lines.
- **Imports** unchanged (the 7 `SM.*` + 6 Mathlib imports of W2); neither unit added one.
- **Other units' sorries untouched**: U5 left `typeII_move`, `typeI_move`, `crossedCusp_move`, `represent` as `sorry`
  (4); U6 left `typeIII_site`, `represent` (2); the merge takes the proved body wherever one unit provides it.

## 3. Layout of `Skeleton_W3.lean`

| lines | content |
|---|---|
| 1-13 | imports (unchanged from W2) |
| 15-149 | header, `namespace SM` (L42), the eight bundles, `namespace FrontRows` (L146), `section Leaves` (L150) |
| 152-11083 | waves 1-2 unchanged: L-deg, L-cnt, U1, U2 record core, **U3** (…L8605), L-rec leaves, **U4** (…L11083) |
| 11085-11092 | the L-geo section docstring (W2 L11085-11092) |
| **11093-13042** | **U5 infrastructure** (`namespace U5` L11095 … `end U5` L13041; 184 declarations: sections A-K of W3_U5_REPORT §2; `SM.FrontRows.U5`, `.U5.Blk`, `.U5.Pair`) |
| 13043-13065 | `typeIII_site` — **proved** (theorem L13050; body L13051-13065: `U5.site₁₂`/`U5.site₂₁` via `realize_eq_realizeAt` + `convert … using 3`) |
| **13067-27391** | **U6 infrastructure** (`namespace U6` L13074 … `end U6` L27390; 1,098 declarations, 11 tactic macros, 116 `local notation`s).  L13067-24171 = the part already ported in `SM/FrontRowsW3.lean` (generic `RISpec`/`riData_of`, `RIISpec`/`riiData_of`, crossed cusp, type I, type II (a)/(c), word level of (b)); **L24172-27390 = the new (b)/(d) tail** (§7): H3-H5 variant (b) (`MvIIb`, `IIbVertices`, `TypeIIbSpec`, `TypeIIbSpec2`), I1-I5 variant (d) (`TypeIIdWord`, `TypeIIdPassage`, `MvIId`, `IIdVertices`, `TypeIIdSpec`, `TypeIIdSpec2`), J the dispatch `typeII_move_proof` (L27376-27387) |
| 27392-27400 | `typeII_move` — **proved** (theorem L27398, `:= U6.typeII_move_proof h`) |
| 27402-27408 | `typeI_move` — **proved** (theorem L27406, `:= U6.typeI_move_proof h`) |
| 27410-27417 | `crossedCusp_move` — **proved** (theorem L27415, `:= U6.crossedCusp_move_proof h`) |
| 27419-28074 | L-PL (U7, wave 1) |
| 28076-29704 | U8D infrastructure + the three deform leaves (wave 2) |
| 29706-30855 | U8R infrastructure (`section U8RInfra` L29720 … L30855; wave 2) |
| 30857-30862 | `represent` — **open** (theorem L30860, `:= sorry` L30862) — the sweep lane's target |
| 30864-31181 | `end Leaves`, glue (`P_comm` L30894 … `P_typeIII` L30909, `P_typeII` L30915, `P_typeI` L30921, `P_crossedCusp` L30927, `skein_ineq_*`), `end FrontRows` L31024, the eight rows (`ng_commutation` L31031, `ng_front_I` L31047, `ng_front_II` L31055, `ng_front_III` L31064, `ng_deletions` L31074, `ng_circle` L31097, `ng_cusp_skein` L31109, `ng_cusp_skein_both` L31126), `certificate_laws` L31139, `word_bound` L31162, `ng_local_front_bound` L31170, `end SM` L31180 (all unchanged from W2) |

Offsets from `Skeleton_W2.lean`: +1,964 for lines W2 ≥ 11103 up to the U6 leaves (…W2 L11128), +16,289 for lines
W2 ≥ 11129 (e.g. `represent` W2 L14571 → L30860; `ng_front_II` W2 L14766 → L31055).

## 4. Remaining leaf (1) — `represent`, and the sweep lane

| leaf | line | unit | consumed by | status |
|---|---|---|---|---|
| `represent` | 30860 | U8R | row 76 field `represent` (`ng_commutation`), row 83 (`ng_local_front_bound` opens with `ng_commutation.represent`) | `sorry` here by instruction.  Proved by the SWEEP lane: `W3S_Merged.lean` (W3S_MERGE_REPORT: `SM.FrontRows.represent` `[propext, Classical.choice, Quot.sound]`, row 76 closed) and already ported as `work/lean/SM/FrontRowsW2S.lean` (0 sorries; `represent` L8553, `ng_commutation` L8586) |

Union with the sweep lane (W3S_MERGE_REPORT §7, recipe A, still valid): `W3S_Merged.lean`'s two hunks against W2 are
`14567a14568,23079` and `14573c23085,23086`; this file's hunks all lie in W2 L11092-11128, strictly before, so
`diff Skeleton_W2.lean Skeleton_W3.lean > /tmp/lgeo.diff; cp W3S_Merged.lean Skeleton_W3_FINAL.lean; patch Skeleton_W3_FINAL.lean /tmp/lgeo.diff`
applies without offset; in this file's coordinates the sweep block goes in after L30856 (the blank before the `represent`
docstring) and replaces L30862.  Expected after the union: `grep -c sorry` = 2 (the two FALSE unused sweep leaves
`dirBit_of_cont_before/after`, W3S §4) and rows 76-83 all free of `sorryAx`.

## 5. `#print axioms` in the merged file (probe copies `/tmp/lean_merge3/W3_ax.lean` = `Skeleton_W3.lean` + 30 `#print axioms` lines, log `/workspace/scratch/merge3_axioms.log`, 0 errors apart from one wrong name of mine — `SM.certificate_laws` is `SM.FrontRows.certificate_laws` — redone in `W3_ax2.lean`, log `merge3_axioms2.log`)

| row | theorem | axioms | status |
|---|---|---|---|
| 76 ng:commutation | `SM.ng_commutation` | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]` | open — only through `represent` (sweep lane) |
| **77 ng:front-I** | `SM.ng_front_I` | **`[propext, Classical.choice, Quot.sound, SM.lp_lm]`** | **CLOSED** (U6 `typeI_move` → `P_typeI`; wave 1 `typeI_counts`) |
| **78 ng:front-II** | `SM.ng_front_II` | **`[propext, Classical.choice, Quot.sound, SM.lp_lm]`** | **CLOSED** (U6 `typeII_move` → `P_typeII`; wave 1 `typeII_counts`) |
| **79 ng:front-III** | `SM.ng_front_III` | **`[propext, Classical.choice, Quot.sound, SM.lp_lm]`** | **CLOSED** (U5 `typeIII_site` → `P_typeIII`; wave 1 `typeIII_counts`) |
| **80 ng:deletions** | `SM.ng_deletions` | **`[propext, Classical.choice, Quot.sound, SM.lp_lm]`** | **CLOSED** (U6 `crossedCusp_move` → `P_crossedCusp` → `crossedCusp_B`; wave 2 `P_zigzag`; wave 1 counts) |
| **81 ng:circle** | `SM.ng_circle` | `[propext, Classical.choice, Quot.sound, SM.lp_lm]` | CLOSED (wave 2) |
| **82 ng:cusp-skein** | `SM.ng_cusp_skein`, `SM.ng_cusp_skein_both` | `[propext, Classical.choice, Quot.sound, SM.lp_lm]` | CLOSED (wave 2) |
| 83 ng:local-front-bound | `SM.ng_local_front_bound` | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]` | open — `sorryAx` now only through `ng_commutation.represent`; `SM.ng_finite_word` is the accepted literature interface consumed by `word_bound` |

Glue and leaves: `P_typeI`, `P_typeII`, `P_typeIII`, `P_crossedCusp`, `P_comm`, `P_zigzag`, `P_circleDeletion` =
`[propext, Classical.choice, Quot.sound, SM.lp_lm]` (the first four carried `sorryAx` in W2).  `typeIII_site`,
`typeII_move`, `typeI_move`, `crossedCusp_move` = `[propext, Classical.choice, Quot.sound]`; `represent` =
`[propext, sorryAx, Classical.choice, Quot.sound]`.  Key new declarations: `U5.Pair.site_of`, `U5.site₁₂`, `U5.site₂₁`,
`U6.typeII_move_proof`, `U6.typeI_move_proof`, `U6.crossedCusp_move_proof`, `U6.riData_of`, `U6.riiData_of` =
`[propext, Classical.choice, Quot.sound]`.
Probe 2 (`W3_ax2.lean`): `SM.FrontRows.certificate_laws` = `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]` and `SM.FrontRows.word_bound` = `SM.ng_local_front_bound` = `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]` — the `sorryAx` enters ONLY through `ng_commutation.comm_B` (L31144): a projection of the single theorem `ng_commutation`, whose `represent` field is the remaining `sorry`, so the whole term carries `sorryAx` although `comm_B` itself is proved; the other 13 fields consumed by `certificate_laws` (`ng_front_I.typeI_B`, `ng_front_II.typeII_B`, `ng_front_III.typeIII_B`, `ng_deletions.zigzag_B/crossedCusp_B`, `ng_circle.circleDeletion_B`, `ng_cusp_skein.earlier_branch`, `base_defect_nonneg`, `wordMoves_*`) come from sorry-free theorems.  Also `skein_ineq_forward`, `skein_ineq_backward`, `base_defect_nonneg` = `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (unchanged).  With the sweep lane's `represent` (§4) rows 76 and 83, `certificate_laws` and `word_bound` become sorry-free without any further change.

## 6. Name-clash scan (task step 5)

`work/drafts/frontrows/clash_scan_w3a.py` (rerun: `python3 clash_scan_w3a.py`; = `clash_scan_w2.py`'s namespace-aware
indexer — tracks `namespace`/`section`/`end`, skips comments — pointed at the two new blocks of `Skeleton_W3.lean`, plus
the pairwise intersections; full list `/tmp/lean_merge3/w3a_new_decls.txt`).  Indexed: U5 block L11093-13041 → **184**
declarations, U6 block L13067-27390 → **1,098**, rest of the skeleton 1,139; 665 `.lean` files under `work/lean` outside `.lake`.

| check | result |
|---|---|
| duplicates inside a block | none (184 and 1,098 distinct fully-qualified names) |
| names outside the block's namespace | none — every U5 name is `SM.FrontRows.U5.*` (66 + `Blk` 81 + `Pair` 37), every U6 name `SM.FrontRows.U6.*` (incl. `RISpec`, `RIISpec`, `NoMeet`, `NonGrid`, `OnlyAtJoint` sub-namespaces) |
| (b) U5 ∩ U6 | **∅** |
| (c) new blocks ∩ rest of `Skeleton_W3.lean` | **∅** (the compile confirms independently: Lean rejects a duplicate) |
| (a) new blocks ∩ `work/lean` | **1,078 same fully-qualified names, ALL in `work/lean/SM/FrontRowsW3.lean`** (184 U5 + 894 U6), **none anywhere else**.  `SM/FrontRowsW3.lean` (13,267 lines, "Ported 17:10Z 2026-09-14 from FrontRows_W3_Delta.lean", W3_DELTA_REPORT.md) is the incremental port of THIS lane: its U5 block (L97-2045) is byte-identical to `Skeleton_W3.lean` L11093-13041, and its U6 block body (L2071-13175, up to `end TypeIIbPassage`) is byte-identical to `Skeleton_W3.lean` L13067-24171; its leaves `typeIII_site`, `typeI_move`, `crossedCusp_move`, consumers `P_typeIII/I/crossedCusp`, rows 77/79/80 and the five row structures are likewise verbatim copies (all checked as contiguous substrings).  So these are the same declarations, not conflicting ones — **no rename needed**; the consequence is only for porting (§7): the next module must import `SM.FrontRowsW3` and not re-declare them |
| the **204 U6 declarations not yet in `work/lean`** (`Skeleton_W3.lean` L24176-27380: `pvA3/pvB3/mvB3`, `IsMovedB`, `mvIIb*`, `bMv`, `tvT3/tvC3_*`, `bII_*`, `bT_*`/`bC_*`, `b_*` (29), `tvT4/tvC4`, `pvA4/pvB4/mvB4`, `IsMovedD`, `mvIId*`, `dMv`, `dT_*`/`dC_*`, `d_*` (66), `dII_*`, `typeII_b`, `typeII_d`, `typeII_move_proof`) | **0 clashes** with anything in `work/lean` |
| global syntax extensions | the U6 block's 11 tactic macros: 9 (`cc_mem` … `cII_pair`) are already declared by `SM/FrontRowsW3.lean` (same text); the 2 new ones **`bII_pair`** (L24369), **`dII_pair`** (L26305) are declared nowhere in `work/lean` (the only other tactic macros there are `labomega`, `idxomega`, `lenomega` in `SM/FrontWordsBase.lean`/`SM/FrontWords.lean`).  No `notation`/`syntax`/`infix` besides the 116 section-local `local notation`s |
| secondary (short names in another namespace) | informational only: 184/184 U5 and 884/1,088 U6 short names also occur in `work/lean` — again all in `SM/FrontRowsW3.lean` under the same namespaces (the U6 remainder are the 204 new ones); no row-level name (`ng_front_II`, `P_typeII`, `certificate_laws`, `word_bound`, `ng_local_front_bound`, `typeII_move`) is declared anywhere in `work/lean` |

## 7. Porting notes (the plan: a sorry-free module for the closed rows)

State of `work/lean` (all three built, `.olean`s present, 0 sorries): `SM/FrontRowsW2.lean` (rows 81, 82 + U1-U4, U7, U8D,
U8R infrastructure), `SM/FrontRowsW2S.lean` (imports W2; the sweep block, `represent`, row 76), `SM/FrontRowsW3.lean`
(imports W2S; the five row structures, U5, the first 11,105 lines of U6, `typeIII_site`, `typeI_move`, `crossedCusp_move`,
`P_typeIII/I/crossedCusp`, rows 77, 79, 80).  Rows 76, 77, 79, 80, 81, 82 are therefore already ported sorry-free.

**What this merge adds for porting = the LAST delta** (W3_DELTA_REPORT §6, suggested `FrontRows_W3F_Delta.lean` →
`work/lean/SM/FrontRowsW3F.lean`, `import SM.FrontRowsW3`), everything verbatim from `Skeleton_W3.lean`:

| # | content | `Skeleton_W3.lean` lines | scope to reproduce |
|---|---|---|---|
| 1 | the new U6 sections: `/-! #### H3 … -/` through `end` (closing the block's `noncomputable section`), i.e. sections `MvIIb`, `IIbVertices`, `TypeIIbSpec`, `TypeIIbSpec2`, `TypeIIdWord`, `TypeIIdPassage`, `MvIId`, `IIdVertices`, `TypeIIdSpec`, `TypeIIdSpec2`, `/-! #### J -/` `typeII_move_proof`, and the namespace-level defs between them (`pvA3`, `pvB3`, `mvB3`, `IsMovedB`, `mvIIb`, …, `pvA4`, …, `dMv`), plus the two macros `bII_pair`, `dII_pair` | **24173-27388** (= `W3_U6.lean` L22209-25424) | `namespace SM` / `open SM.FrontWord SM.Link` / `open scoped ContDiff` / `namespace FrontRows` / `section Leaves` / **`namespace U6` / `open SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4` / `noncomputable section`** … `end` / `end U6` |
| 2 | the leaf `typeII_move` (docstring + statement + `:= U6.typeII_move_proof h`), then `end Leaves` | 27392-27400 | `SM.FrontRows` (`section Leaves`) |
| 3 | `P_typeII` | 30915-30920 | `namespace FrontRows` after `end Leaves` |
| 4 | row 78 `ng_front_II : NgFrontIIClauses` | 31055-31063 | `namespace SM` after `end FrontRows` + `open FrontRows` (structure already in `FrontRowsW3`) |
| 5 | the row-83 docstring, `certificate_laws`, `word_bound` | 31131-31165 (`namespace FrontRows` … `end FrontRows`) | `SM.FrontRows` |
| 6 | row 83 `ng_local_front_bound : NgLocalFrontBoundClauses`, `end SM` | 31166-31180 | `namespace SM` |

Facts checked here that the porter can rely on:
- The tail L24172-27390 is **self-contained** relative to the ported part: it is a sequence of closed `section`s (each with
  its own `variable`s and `local notation`s — `local notation`s are section-scoped, so nothing there can depend on one from
  an earlier section) and namespace-level `def`s; it uses the imported macros (`tIIL_mem`, `tIIR_mem`, `aII_pair`, …) and
  `U6.*`/`U3.*`/`U4.*`/`U2.*` lemmas by name, all of which are in `SM.FrontRowsW3`/`W2` after the import.  The (b)-word-level
  sections `TypeIIbWord`, `TypeIIbPassage` (L23540-24171) are already ported — do NOT copy them again.
- **Must NOT be re-declared**: the 1,078 names of §6 (in particular `U6.typeII_a`, `U6.typeII_c`, `U6.riiData_of`,
  `U6.riData_of`, `U6.typeI_move_proof`, `U6.crossedCusp_move_proof`, `U6.bT`, `U6.bC`, `U6.b_bits`, `U6.b_A1..`, `U6.b_passage`,
  `U6.b_hexit`, `U6.b_sameEffect`, the `c'_L*` lemmas), the nine macros `cc_mem` … `cII_pair`, the five `Ng*Clauses`
  structures, `typeIII_site`, `typeI_move`, `crossedCusp_move`, `P_typeIII/I/crossedCusp`, `ng_front_I/III`, `ng_deletions`
  (all `FrontRowsW3`), `NgCommutationClauses`, `ng_commutation`, `represent`, the 595 `U8R` sweep declarations (`FrontRowsW2S`),
  and the W2_CLEAN_REPORT §3 list (`FrontRowsW2`).  Regenerate the lists with `clash_scan_w2.py`, `clash_scan_w2s.py`,
  `clash_scan_w3.py`; this scan's new-block list is `/tmp/lean_merge3/w3a_new_decls.txt` (the 204 unported ones are those
  with line ≥ 24172).
- The 22 linter warnings in the tail (Skeleton_W3 L25177-25502 and L27114-27274: unused `omega`s, "never executed",
  `c`/`c'` not referenced) are cosmetic and pre-existing in `W3_U6.lean`; they can be kept verbatim (decision D-FR1 style:
  body verbatim) or cleaned in a separate pass — never while porting.
- Expected checks for the last delta (W3_DELTA_REPORT §6): `grep -c -i sorry` = 0; 0 errors; `#print axioms`:
  `SM.FrontRows.typeII_move` standard three; `SM.ng_front_II`, `SM.FrontRows.certificate_laws` `+ SM.lp_lm`;
  `SM.FrontRows.word_bound`, `SM.ng_local_front_bound` `+ SM.lp_lm, SM.ng_finite_word` — these are exactly the values
  measured in this merged file (§5), with `represent` supplied by `FrontRowsW2S` instead of the skeleton's `sorry`.
- Alternative (one module instead of a fourth delta): a `clean_w2.py`-style pass over the FINAL union file of §4
  (`Skeleton_W3.lean` + the sweep hunks) would give one 39k-line sorry-free module for rows 76-83; the incremental route
  above is far cheaper to compile and check, and three quarters of it is already built.

## 8. Files

- `work/drafts/frontrows/Skeleton_W3.lean` — the merged file (31,181 lines, 1 sorry).
- `work/drafts/frontrows/merge3.py` — regenerates it from `Skeleton_W2.lean` + `W3_U5.lean` + `W3_U6.lean` (with the unit-verification checks of §2).
- `work/drafts/frontrows/clash_scan_w3a.py` — the namespace-aware clash scan of §6.
- `/workspace/scratch/merge3_compile.log` (compile), `merge3_axioms.log`, `merge3_axioms2.log` (probes); `/tmp/lean_merge3/W3_ax.lean`, `W3_ax2.lean`, `w3a_new_decls.txt` (ephemeral).
