# W3_DELTA_REPORT — certificate rows lane, wave-3 delta: the front-move leaves `typeIII_site`, `typeI_move`, `crossedCusp_move`, rows 77 ng:front-I, 79 ng:front-III, 80 ng:deletions, and the five row-statement structures

2026-09-14 17:09 UTC / 1:09pm ET.  Inputs: `work/drafts/frontrows/W3_U5.lean` (16,855 lines, W3_U5_REPORT.md), `work/drafts/frontrows/W3_U6.lean`
(26,000 lines, W3_U6_REPORT.md; `W3_U6b.lean` is byte-identical to it), `work/drafts/frontrows/Skeleton_W2.lean` (14,891 lines), and the
built modules `work/lean/SM/FrontRowsW2.lean` (= `FrontRows_W2_Clean.lean` + 1 "Ported" line) and `work/lean/SM/FrontRowsW2S.lean`
(= `FrontRows_W2S_Delta.lean` + 1 "Ported" line; `diff` checked).
Output: **`work/drafts/frontrows/FrontRows_W3_Delta.lean`** (13,266 lines), produced by **`work/drafts/frontrows/delta_w3.py`**
(rerunnable; asserts ~60 text anchors on the three source files — including that each unit file equals the skeleton outside its
reported hunks — assembles, asserts byte-identity of every copied range, scans for forbidden tokens, writes the line map
`/tmp/w3delta/linemap.json` and the axiom probe `/tmp/w3delta/W3_ax.lean`).  Intended destination once accepted:
`work/lean/SM/FrontRowsW3.lean` (module `SM.FrontRowsW3`).  Nothing under `work/lean` was touched; no `lake build`; compiled in
place with `cd work/lean && lake env lean ../drafts/frontrows/FrontRows_W3_Delta.lean`.  Scratch: `/tmp/w3delta/`.

## 1. Result

| item | value |
|---|---|
| file | `work/drafts/frontrows/FrontRows_W3_Delta.lean`, **13,266 lines**; imports **only** `SM.FrontRowsW2S` (the import lists of `W3_U5.lean`, `W3_U6.lean`, `Skeleton_W2.lean` and `SM/FrontRowsW2.lean` are identical — 7 `SM.*` + 6 Mathlib modules — so nothing beyond the transitive imports of `FrontRowsW2S` is needed; the U6 report lists no added import) |
| `grep -c -i sorry` | **0** (code and docstrings; the header is new and describes the module) |
| `#print` / `#eval` / `#check` / `set_option` lines | **0** (`grep -c -E '#print\|#eval\|#check\|set_option'`); also no `axiom`, `unsafe`, `private` in the copied blocks |
| compile | **0 errors, exit 0**, 68 s wall (log `/tmp/w3delta/compile_delta.log`) |
| warnings | **32, all pre-existing** in the U6 block: mapped by +9033 to `W3_U6.lean` they are exactly the 32 U6-block linter warnings of that file's compile (`/tmp/u6/full3.log`: 39 = 3 `declaration uses sorry` + 4 U8R + 32 U6) — 22 × "Unused tactic linter: `omega` does nothing", 4 × "this tactic is never executed", 6 × "Variable name `c`/`c'` is not explicitly referenced", 2 × "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice" (delta L6378, 6448, 7801, 7871, 8646×2, 8785, 10280×2, 10282×2, 10297, 10324, 10351, 10378, 10415, 10440, 10623×2, 10755, 12259×2, 12261×2, 12276, 12303, 12330, 12357, 12394, 12419, 12583×2).  The U5 block compiles with zero warnings (as in W3_U5_REPORT).  **No** `declaration uses sorry` |
| axioms (probe `/tmp/w3delta/W3_ax.lean` = module + 17 `#print axioms` lines; log `/tmp/w3delta/compile_ax.log`, 0 errors, 70 s) | **`SM.ng_front_I`, `SM.ng_front_III`, `SM.ng_deletions`: `[propext, Classical.choice, Quot.sound, SM.lp_lm]`** (as expected; `lp_lm` is the accepted literature interface reached through `P`, present already in the types of the `Ng*Clauses` structures).  **`SM.FrontRows.typeIII_site`, `typeI_move`, `crossedCusp_move`: `[propext, Classical.choice, Quot.sound]`.**  Also `P_typeIII`, `P_typeI`, `P_crossedCusp`: the four with `lp_lm`; `U5.Pair.site_of`, `U6.typeI_move_proof`, `U6.crossedCusp_move_proof`: the standard three.  No `sorryAx` anywhere |
| name clashes against `work/lean` (incl. `SM/FrontRowsW2.lean`, `SM/FrontRowsW2S.lean`) | **none** (§5) |
| top-level declarations | **1,092** (all distinct fully-qualified names): 989 theorems, 87 defs, 9 structures, 7 abbrevs — 184 in `SM.FrontRows.U5(.Blk/.Pair)`, 894 in `SM.FrontRows.U6(.RISpec/.RIISpec/.NoMeet/.NonGrid/.OnlyAtJoint)`, 6 in `SM.FrontRows` (3 leaves, 3 consumers), 8 in `SM` (5 structures, 3 rows).  Plus **nine global tactic macros** declared by the U6 block (§5) |

`ng_deletions` does NOT depend on `typeII_move`: its body (skeleton L14785-14803, verbatim) cites `realize_sCount`, `IsZigzagDeletion.source_ne_nil`,
`IsZigzagDeletion.ne_nil`, `zigzag_counts`, `P_zigzag`, `IsCrossedCuspShortcut.ne_nil`, `crossedCusp_counts` (all in `SM.FrontRowsW2`) and
`P_crossedCusp` (this module, from `crossedCusp_move`); the axiom check confirms (no `sorryAx`, and `typeII_move` is not declared at all).
Neither do `ng_front_I` (`typeI_counts`, `P_typeI`) nor `ng_front_III` (`typeIII_counts`, `P_typeIII`).  No STOP condition was met.

## 2. Layout of the delta module and provenance (exact line ranges)

Nesting reproduced from the skeleton at each point: the structures sit in `namespace SM` (skeleton L42, with `open SM.FrontWord SM.Link`,
`open scoped ContDiff`, L44-45) before `namespace FrontRows` (L146); the L-geo region sits in `namespace FrontRows` → `section Leaves` (L150 …
`end Leaves` L14575) directly after `end U4` (L11083), with nothing opened or bound at column 0 between `section Leaves` and it outside closed
sections/namespaces (stack-tracking scan of the skeleton; the only column-0 `open`s are L44-45 and `open FrontRows` L14737); the consumers sit
in `namespace FrontRows` after `end Leaves` (no `section`/`open` between L14575 and L14619); the rows sit after `end FrontRows` (L14735) +
`open FrontRows` (L14737).  The unit blocks carry their own `namespace U5`/`U6`, `open`s, `noncomputable section` and (U6) 88 section-local
`local notation`s, all in closed sections.

| delta lines | content | source (verbatim unless "new") |
|---|---|---|
| 1 | `import SM.FrontRowsW2S` | new |
| 3-42 | module header `/-! # Front certificate rows — wave-3 delta: the front-move leaves and rows 77, 79, 80 … -/` (40 lines; describes the module, lists what is NOT in it incl. `typeII_move`) | new |
| 44, 46-47 | `namespace SM`, `open SM.FrontWord SM.Link`, `open scoped ContDiff` | = skeleton L42, 44, 45 |
| 49 | `/-! ## Statements of rows 77, 78, 79, 80 and 83 … -/` | new heading |
| **51-79** | **`structure NgFrontIClauses`** 51-52, blank 53, **`NgFrontIIClauses`** 54-60, blank 61, **`NgFrontIIIClauses`** 62-68, blank 69, **`NgDeletionsClauses`** 70-78, blank 79 | **skeleton L74-102** (offset −23), byte-identical (`cmp` of `/tmp/w3delta/structs_delta.txt` vs `structs_skel.txt`) |
| **80-83** | **`structure NgLocalFrontBoundClauses`** 80-82, blank 83 | **skeleton L119-122** (offset −39), byte-identical (same `cmp`) |
| 84, 86 | `namespace FrontRows`, `section Leaves` | = skeleton L146, 150 |
| 88-95 | the L-geo section docstring `/-! ### L-geo (units U5, U6 on the geometry core U4) … -/` + blank | skeleton L11085-11092 (offset −10997) |
| **96-2045** | **the U5 block**: `/-! ### U5 infrastructure -/` 96, `namespace U5` 98, … `end` 2042, `end U5` 2044, blank 2045 (184 declarations) | **`W3_U5.lean` L11093-13042** (offset −10997), byte-identical (`cmp`) |
| **2046-2069** | **the leaf `typeIII_site`**: docstring 2046-2052, `theorem typeIII_site … :` **2053**, statement line + `:= by` 2054, proved body 2055-2068 (14 lines: `U5.site₁₂`/`U5.site₂₁` via `realize_eq_realizeAt` + `convert … using 3`), blank 2069 | **`W3_U5.lean` L13043-13066** (offset −10997), byte-identical; statement text = skeleton L11100-11101 with `:= sorry` → `:= by` |
| **2070-13178** | **the U6 block**: `/-! ### U6 infrastructure -/` 2070, unit docstring 2072-2075, `namespace U6` 2077, `open SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4` 2079, `noncomputable section` 2081, sections `Helpers` … `TypeIIbPassage`, `end` 13175, `end U6` 13177, blank 13178 (894 declarations, 9 tactic macros, 88 `local notation`s) | **`W3_U6.lean` L11103-22211** (offset −9033), byte-identical (`cmp`) |
| 13179-13181 | 2-line `/-! The leaf typeII_move … is not in this module … -/` note + blank, in place of the omitted leaf | new (replaces `W3_U6.lean` L22212-22221 = skeleton L11103-11112, §3) |
| **13182-13189** | **the leaf `typeI_move`**: docstring 13182-13185, `theorem typeI_move` **13186**-13187, body `:= U6.typeI_move_proof h` 13188, blank 13189 | **`W3_U6.lean` L22222-22229** (offset −9033), byte-identical; statement = skeleton L11117-11119 with `:= sorry` → `:= U6.typeI_move_proof h` |
| **13190-13198** | **the leaf `crossedCusp_move`**: docstring 13190-13194, `theorem crossedCusp_move` **13195**-13196, body `:= U6.crossedCusp_move_proof h` 13197, blank 13198 | **`W3_U6.lean` L22230-22238** (offset −9033), byte-identical; statement = skeleton L11126-11128 likewise |
| 13199 | `end Leaves` | = skeleton L14575 |
| 13201 | `/-! ## Glue: the polynomial consumers … -/` | new heading |
| **13203-13208** | **`P_typeIII`**: docstring 13203, theorem **13204**-13207 (`typeIII_site` + `P_reidemeister_III`), blank 13208 | skeleton L14619-14624 (offset −416), byte-identical |
| **13209-13214** | **`P_typeI`**: docstring 13209, theorem **13210**-13213 (`typeI_move` + `P_reidemeister_I` + `presentations`), blank | skeleton L14631-14636 (offset −422), byte-identical |
| **13215-13220** | **`P_crossedCusp`**: docstring 13215, theorem **13216**-13219 (`crossedCusp_move` + `P_reidemeister_I` + `presentations`), blank | skeleton L14637-14642 (offset −422), byte-identical |
| 13221, 13223 | `end FrontRows`, `open FrontRows` | = skeleton L14735, 14737 |
| 13225 | `/-! ## Assembly of rows 77, 79 and 80 … -/` | new heading |
| **13227-13234** | docstring 13227; **`theorem ng_front_I : NgFrontIClauses where`** **13228**-13233; blank 13234 | **skeleton L14757-14764** (offset −530), byte-identical (`cmp` of `/tmp/w3delta/rows_delta.txt` vs `rows_skel.txt`) |
| **13235-13243** | docstring 13235; **`theorem ng_front_III : NgFrontIIIClauses where`** **13236**-13242; blank 13243 | **skeleton L14774-14782** (offset −539), byte-identical (same `cmp`) |
| **13244-13265** | docstring 13244-13245; **`theorem ng_deletions : NgDeletionsClauses where`** **13246**-13264; blank 13265 | **skeleton L14783-14804** (offset −539), byte-identical (same `cmp`) |
| 13266 | `end SM` | = skeleton L14891 |

**Verbatim checks** (asserted by `delta_w3.py` and repeated with external `cmp`): delta L51-83 == skeleton L74-102 ++ L119-122; L88-95 == skeleton
L11085-11092; L96-2045 == W3_U5 L11093-13042; L2046-2069 == W3_U5 L13043-13066; L2070-13178 == W3_U6 L11103-22211; L13182-13189 == W3_U6
L22222-22229; L13190-13198 == W3_U6 L22230-22238; L13203-13220 == skeleton L14619-14624 ++ L14631-14642; L13227-13265 == skeleton L14757-14764 ++
L14774-14804.  The script also asserts that `W3_U5.lean` = skeleton outside the hunks `11092a11093,13042` / `11101c13051,13065` and `W3_U6.lean` =
skeleton outside `11102a11103,22211` / `11119c22228` / `11128c22237` (so the blocks are exactly the units' additions), and that every copied unit
line is free of `sorry` (case-insensitive), `#print`, `#eval`, `#check`, `set_option`.

Helpers cited and where they are: `typeIII_site` → `U5.band`, `U5.site₁₂`, `U5.site₂₁` (this module), `realize_eq_realizeAt` (library);
`typeI_move` → `U6.typeI_move_proof`; `crossedCusp_move` → `U6.crossedCusp_move_proof` (this module).  The U5/U6 blocks depend only on the
skeleton up to `end U4` (= `SM.FrontRowsW2`: U1-U4, the library), as their reports state (both were developed against prefix `.olean`s);
the compile against the full `FrontRowsW2S` import (which additionally exposes `SM.FrontRows.represent`, the glue `P_comm`…, U7/U8D/U8R) raised
no ambiguity.  The consumers cite `P_reidemeister_I/III`, `presentations` (accepted library, `SM`); the rows cite `typeI_counts`, `typeIII_counts`,
`zigzag_counts`, `crossedCusp_counts`, `P_zigzag`, `IsZigzagDeletion.source_ne_nil/ne_nil`, `IsCrossedCuspShortcut.ne_nil`, `realize_sCount`
(all in `SM.FrontRowsW2`, reached through `open FrontRows` / `SM.FrontWord`).

## 3. Omitted (left for the last delta, §6)

| skeleton lines | declaration | why omitted |
|---|---|---|
| 11103-11112 (= W3_U6 L22212-22221) | `SM.FrontRows.typeII_move` (docstring + statement, body still `sorry` in W3_U6) | its variants (b), (d) are being proved by a follow-up unit; replaced in place by the 2-line note at delta L13179-13180 and named in the header |
| 14625-14630 | `SM.FrontRows.P_typeII` | consumes `typeII_move` |
| 14765-14773 | `SM.ng_front_II` (row 78) | consumes `P_typeII` |
| 14842-14877 | `namespace FrontRows` wrapper, row-83 docstring, `certificate_laws`, `word_bound`, `end FrontRows` | `certificate_laws` consumes `ng_front_II` |
| 14878-14890 | `SM.ng_local_front_bound` (row 83) | consumes `word_bound` |

Nothing else of the skeleton's L-geo region or of the W2_CLEAN_REPORT §3 list is missing from the three modules now: rows 1-6 (structures) are in
`FrontRowsW2S` (1) and here (2-6); 7, 9, 10, 12, 14, 15, 17, 19, 20 are here; 11, 16 are in `FrontRowsW2S`; 8, 13, 18, 21, 22, 23 are the last delta.

## 4. Statement declarations in the delta (FrontRows_W3_Delta.lean line numbers)

| declaration | kind | delta line | notes |
|---|---|---|---|
| **`SM.NgFrontIClauses`** | structure (row 77 statement, used by `ng_front_I`) | **51**-52 | field `typeI_B`; = skeleton L74-75 |
| `SM.NgFrontIIClauses` | structure (row 78 statement; for the last delta) | 54-60 | fields `typeII_D/w/d/B`; = skeleton L77-83 |
| **`SM.NgFrontIIIClauses`** | structure (row 79 statement, used by `ng_front_III`) | **62**-68 | fields `typeIII_D/w/d/B`; = skeleton L85-91 |
| **`SM.NgDeletionsClauses`** | structure (row 80 statement, used by `ng_deletions`) | **70**-78 | fields `zigzag_s/B`, `crossedCusp_s/B`; = skeleton L93-101 |
| `SM.NgLocalFrontBoundClauses` | structure (row 83 statement; for the last delta) | 80-82 | field `front_inequality`; = skeleton L119-121 |
| **`SM.ng_front_I`** | theorem `: NgFrontIClauses` | docstring 13227, **13228**-13233 | = skeleton L14757-14763 |
| **`SM.ng_front_III`** | theorem `: NgFrontIIIClauses` | docstring 13235, **13236**-13242 | = skeleton L14774-14781 |
| **`SM.ng_deletions`** | theorem `: NgDeletionsClauses` | docstring 13244-13245, **13246**-13264 | = skeleton L14783-14803 |
| `SM.FrontRows.typeIII_site` | theorem (leaf, U5) | docstring 2046-2052, **2053**-2068 | statement = skeleton L11100-11101 |
| `SM.FrontRows.typeI_move` | theorem (leaf, U6) | docstring 13182-13185, **13186**-13188 | statement = skeleton L11117-11119 |
| `SM.FrontRows.crossedCusp_move` | theorem (leaf, U6) | docstring 13190-13194, **13195**-13197 | statement = skeleton L11126-11128 |
| `SM.FrontRows.P_typeIII` / `P_typeI` / `P_crossedCusp` | theorems (consumers) | **13204** / **13210** / **13216** | = skeleton L14620 / 14632 / 14638 |

(The executor's port prepends one "Ported …" comment line, as for `FrontRowsW2` and `FrontRowsW2S`; every number above then shifts by +1 in
`work/lean/SM/FrontRowsW3.lean`.)

## 5. Name-clash scan (namespace-aware)

`work/drafts/frontrows/clash_scan_w3.py` (= `clash_scan_w2s.py` pointed at this delta, plus explicit per-module intersections and a scan of global
syntax extensions; log `/tmp/w3delta/clash_scan.log`, full list `/tmp/w3delta/delta_decls.txt`): builds the fully-qualified name (tracking
`namespace`/`section`/`end`, skipping comments) of every top-level declaration of the delta (1,092, all distinct — no duplicate inside the file)
and of every `.lean` under `work/lean` outside `.lake` (664 files, **including `SM/FrontRowsW2.lean` (1,116) and `SM/FrontRowsW2S.lean` (598)**),
and intersects.  **Result: 0 clashes**; the explicit delta ∩ `FrontRowsW2.lean` and delta ∩ `FrontRowsW2S.lean` intersections are both empty.
Namespaces used: `SM.FrontRows.U6` (861 + `RIISpec` 15, `RISpec` 12, `NoMeet` 3, `NonGrid` 2, `OnlyAtJoint` 1), `SM.FrontRows.U5` (66 + `Blk` 81,
`Pair` 37), `SM` (8), `SM.FrontRows` (6).  Secondary short-name check (any namespace) for the 14 named declarations, for `typeII_move`, `P_typeII`,
`ng_front_II`, `certificate_laws`, `word_bound`, `ng_local_front_bound`, and for the block-level names `band`, `bandL`, `Blk`, `Pair`, `site_of`,
`swp`, `ptv`, `ExtSl`, `RISpec`, `RIISpec`, `riData_of`, `riiData_of`, `typeI_move_proof`, `crossedCusp_move_proof`, `typeII_a`, `typeII_c`,
`typeII_move_proof`, `mvDiagram`, `rlDiagram`: no declaration of any of them anywhere in `work/lean` (the only coincidences are the expected
`SM.ng_commutation`, `SM.NgCommutationClauses`, `SM.FrontRows.represent`, `SM.FrontRows.U8R.sweep_proof` of `FrontRowsW2S` and the four
unrelated `recordIso`s, none re-declared here).  The compile confirms independently (Lean rejects a duplicate declaration).

**Global syntax extensions.**  The U6 block declares nine tactic macros without `local`/`scoped`, so importers see them: `cc_mem` (delta L3149),
`ccr_mem` (4249), `tI_mem` (5461), `tI_pair` (5812), `tU_pair` (7270), `tIIL_mem` (8450), `tIIR_mem` (8456), `aII_pair` (9470), `cII_pair`
(11458).  None of these tokens is declared (or even mentioned) anywhere else in `work/lean` (the only other tactic macros are `labomega` (local),
`idxomega`, `lenomega` in `SM/FrontWordsBase.lean` / `SM/FrontWords.lean`).  They are kept verbatim (making them `local` would change the block);
the last delta must not re-declare them (§6).  The U5 block declares no syntax.

## 6. Recipe for the LAST delta (rows 78 and 83; `import SM.FrontRowsW3`)

Written once the follow-up unit delivers `typeII_move` proved — expected as a file `W3_U6*.lean` = `W3_U6.lean` + new sections inside the U6
block (`U6.typeII_b`, `U6.typeII_d`, `U6.typeII_move_proof`, with their helpers) + the leaf body `:= U6.typeII_move_proof h` (W3_U6_REPORT
"What remains").  Suggested name `FrontRows_W3F_Delta.lean` → `work/lean/SM/FrontRowsW3F.lean` (or `SM.FrontRowsFinal`).  It `import SM.FrontRowsW3`
(which transitively imports `SM.FrontRowsW2S`, `SM.FrontRowsW2` and everything else) and contains, in this order, with the SAME preamble
(`namespace SM`, `open SM.FrontWord SM.Link`, `open scoped ContDiff`):

| # | content | source (verbatim) | scope |
|---|---|---|---|
| 1 | `namespace FrontRows`, `section Leaves`; **the new U6 helpers only**: `namespace U6`, `open SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4`, `noncomputable section`, then exactly the hunks of `diff W3_U6.lean <follow-up file>` that fall inside the block (new sections; each must carry its own `variable`s/`local notation`s, as the existing sections do — the block's are section-local and closed), `end`, `end U6` | the follow-up unit's file (hunks vs `W3_U6.lean`) | `SM.FrontRows.U6` |
| 2 | the leaf **`typeII_move`**: docstring + statement `Skeleton_W2.lean` L11103-11111 with the body `:= U6.typeII_move_proof h` (as in the follow-up file); `end Leaves` | skeleton L11103-11112 / follow-up file | `SM.FrontRows` |
| 3 | the consumer **`P_typeII`** | skeleton L14625-14630 | `namespace FrontRows` (after `end Leaves`) |
| 4 | `end FrontRows`, `open FrontRows`; row 78 **`ng_front_II : NgFrontIIClauses`** (the structure is already here, delta L54) | skeleton L14765-14773 | `namespace SM` |
| 5 | `namespace FrontRows`, the row-83 docstring, **`certificate_laws`**, **`word_bound`**, `end FrontRows` | skeleton L14842-14877 | `SM.FrontRows` |
| 6 | row 83 **`ng_local_front_bound : NgLocalFrontBoundClauses`** (structure already here, delta L80), `end SM` | skeleton L14878-14891 | `namespace SM` |

It must **NOT** re-declare anything from the three ported modules: from `SM.FrontRowsW3` (this module) the five structures, the three leaves,
the three consumers, the three rows, all 184 `SM.FrontRows.U5.*` and 894 `SM.FrontRows.U6.*` declarations (in particular `U6.typeII_a`,
`U6.typeII_c`, `U6.riiData_of`, `U6.typeI_move_proof`, `U6.crossedCusp_move_proof`, the `TypeIIbWord`/`TypeIIbPassage` word-level (b) lemmas
`bT`, `bC`, `b_bits`, `b_A1..b_A22`, `b_passage`, `b_hexit`, `b_sameEffect`, and the `c'_L*` lemmas of `TypeIIcPassage`), and the nine tactic
macros `cc_mem` … `cII_pair` (the new helpers may USE them — they are imported); from `SM.FrontRowsW2S` `NgCommutationClauses`, `ng_commutation`,
`represent` and the 595 `SM.FrontRows.U8R` sweep declarations; from `SM.FrontRowsW2` the W2_CLEAN_REPORT §3 "must NOT be re-declared" list.
Regenerate the three name lists with `python3 clash_scan_w2.py` / `clash_scan_w2s.py` / `clash_scan_w3.py` (→ `/tmp/w2clean/clean_decls.txt`,
`/tmp/w2sdelta/delta_decls.txt`, `/tmp/w3delta/delta_decls.txt`).  If the follow-up unit's new sections re-open a `variable` block of an
existing section or refer to a `local notation` of one (e.g. `Vb`, `Pb`, `Vc`), they must re-declare it inside their own section (the U6 block
already does this three times for `Vc`).  Name resolution is unchanged: inside `namespace SM.FrontRows`, `certificate_laws` reaches
`ng_commutation`, `ng_front_I`, `ng_front_II`, `ng_front_III`, `ng_deletions`, `ng_circle`, `ng_cusp_skein` (all `SM.*`, from the three modules)
and `base_defect_nonneg` (`SM.FrontRows`, `FrontRowsW2`); `ng_local_front_bound` reaches `ng_commutation.represent` and `FrontRows.word_bound`
exactly as in the skeleton.  Expected checks: `grep -c -i sorry` = 0; 0 errors; `#print axioms` on a `/tmp` copy — `SM.FrontRows.typeII_move`:
`[propext, Classical.choice, Quot.sound]`; `SM.ng_front_II`, `SM.FrontRows.certificate_laws`: `[propext, Classical.choice, Quot.sound, SM.lp_lm]`;
`SM.FrontRows.word_bound`, `SM.ng_local_front_bound`: `[propext, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]` (`ng_finite_word` is
the accepted literature interface consumed by `word_bound` through `ng_finite_word_bound`; W2S_DELTA_REPORT §6); clash scan against `work/lean`
including `SM/FrontRowsW2.lean`, `SM/FrontRowsW2S.lean`, `SM/FrontRowsW3.lean` = 0.  Use the same `delta_w3.py`-style anchored assembly so every
range is verified byte-for-byte.

## 7. Files

- `work/drafts/frontrows/FrontRows_W3_Delta.lean` — the module (13,266 lines).
- `work/drafts/frontrows/delta_w3.py` — regenerates it from `W3_U5.lean` + `W3_U6.lean` + `Skeleton_W2.lean` (anchored; byte-identity asserted) and writes the axiom probe and the line map.
- `work/drafts/frontrows/clash_scan_w3.py` — the namespace-aware clash scan incl. the syntax-extension scan (§5).
- `/tmp/w3delta/` — `compile_delta.log`/`.time`, `compile_ax.log`/`.time`, `W3_ax.lean`, `clash_scan.log`, `delta_decls.txt`, `linemap.json`, the `cmp` extracts `structs_delta/skel.txt`, `rows_delta/skel.txt` (ephemeral).
