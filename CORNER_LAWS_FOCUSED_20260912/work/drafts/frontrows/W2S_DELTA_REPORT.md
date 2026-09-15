# W2S_DELTA_REPORT — certificate rows lane, sweep delta: the leaf `represent` and row 76 ng:commutation

2026-09-14 15:44 UTC / 11:44am ET.  Inputs: `work/drafts/frontrows/W3S_Merged.lean` (23,404 lines, the sweep-lane merge, W3S_MERGE_REPORT.md),
`work/drafts/frontrows/Skeleton_W2.lean` (14,891 lines), and the built module `work/lean/SM/FrontRowsW2.lean`
(= `FrontRows_W2_Clean.lean` + the executor's one-line "Ported" comment; W2_CLEAN_REPORT.md).
Output: **`work/drafts/frontrows/FrontRows_W2S_Delta.lean`** (8,600 lines), produced by
**`work/drafts/frontrows/delta_w2s.py`** (rerunnable; asserts 30 text anchors on the two source files, assembles, checks
byte-identity of every copied range, and writes the axiom probe `/tmp/w2sdelta/W2S_ax.lean`).  Intended destination once
accepted: `work/lean/SM/FrontRowsW2S.lean` (module `SM.FrontRowsW2S`).  Nothing under `work/lean` was touched; no `lake build`;
compiled in place with `cd work/lean && lake env lean ../drafts/frontrows/FrontRows_W2S_Delta.lean`.  Scratch: `/tmp/w2sdelta/`.

## 1. Result

| item | value |
|---|---|
| file | `work/drafts/frontrows/FrontRows_W2S_Delta.lean`, **8,600 lines**; imports **only** `SM.FrontRowsW2` (its import list is identical to `W3S_Merged.lean`'s, so nothing else is needed) |
| `grep -c -i sorry` | **0** (code and docstrings; the two `sorry` leaves of the merged file are removed, §3) |
| `#print` / `#eval` / `#check` / `set_option` lines | none (`grep -c -E '#print\|#eval\|#check\|set_option'` = 0) |
| compile | **0 errors, exit 0**, 40.6 s wall (log `/tmp/w2sdelta/compile_delta.log`) |
| warnings | 51, **all pre-existing**: mapped back to `W3S_Merged.lean` line numbers they are exactly the merged file's 53 warnings inside the sweep block minus the two `declaration uses sorry` of the removed leaves — 38 × deprecated `if_pos`/`if_neg` (S6a/S6b), 7 × unused simp argument (S6a/S6b), 6 × "Variable name … not explicitly referenced" (SweepDefs, S4a, S6a).  **No** `declaration uses sorry` |
| axioms (probe `/tmp/w2sdelta/W2S_ax.lean` = module + 7 `#print axioms` lines; log `/tmp/w2sdelta/compile_ax.log`, 0 errors) | **`SM.ng_commutation`: `[propext, Classical.choice, Quot.sound, SM.lp_lm]`** (as expected; `lp_lm` is the accepted literature interface reached through `P`, also present in the type of `NgCommutationClauses` itself).  **`SM.FrontRows.represent`: `[propext, Classical.choice, Quot.sound]`**.  Also `SM.FrontRows.U8R.sweep_proof`, `U8R.recordIso`, `U8R.s1b_dirBit_of_cont_before`, `U8R.s1b_dirBit_of_cont_after`: `[propext, Classical.choice, Quot.sound]`.  No `sorryAx` anywhere |
| name clashes against `work/lean` (incl. `SM/FrontRowsW2.lean`) | **none** (§5) |
| top-level declarations | **598** (all distinct fully-qualified names): 595 in `SM.FrontRows.U8R`, 1 in `SM.FrontRows` (`represent`), 2 in `SM` (`NgCommutationClauses`, `ng_commutation`) |

## 2. Layout of the delta module and provenance (exact line ranges)

Nesting reproduced from the merged file: the sweep block sits there inside `namespace SM` (L42, with `open SM.FrontWord SM.Link`,
`open scoped ContDiff`) → `namespace FrontRows` (L146) → `section Leaves` (L150) → `namespace U8R` (L14591, its own `open` and
`noncomputable section`); nothing else is opened or bound between `section Leaves` and the block (no `open`/`variable` at column 0
in L150-14567 outside closed sections/namespaces).  `FrontRowsW2` declares no `private` items and its `local notation`s all live in
closed U2/U3 sections, so nothing the block cites is lost across the `import`.

| delta lines | content | source |
|---|---|---|
| 1 | `import SM.FrontRowsW2` | new |
| 3-33 | module header `/-! # Front certificate rows — sweep delta: the leaf represent and row 76 ng:commutation … -/` | new (no "sorry", no `#print` literal) |
| 35-42 | `namespace SM`, `open SM.FrontWord SM.Link`, `open scoped ContDiff`, `namespace FrontRows`, `section Leaves` | = merged L42, 44-45, 146, 150 |
| **44-8548** | **the U8R sweep block**, verbatim: header docstring 44-66, `namespace U8R` 67, `open SM.FrontWord SM.FrontWord.Letter SM.FrontRealize Equiv` 69, `noncomputable section` 71, `section SweepDefs` 73-326, `section SweepLeaves` 328-3423 (S1a helpers 335-407, S1a leaves, MERGER note 603, S2 helpers 608-856 + S2 leaves, S3S5 helpers 920-1113 + S3 leaf, MERGER note 1157, S1b helpers 1160-2134, S1b leaves 2136-2250 with the removal note at **2185-2186**, S4a helpers 2254-2707 + S4a leaves, S4b helpers 2885-3257, `cutBefore_first`/`cutAfter_last`/`run_take_eq_hybrid`, MERGER note 3319, `word_closed` 3324 / `oword` 3339 / `oword_letters`, `word_ne_nil` … `cut_word_colAt`), `section SlotMap` 3427-3610, `section Traversal` 3614-8521 (S6a helpers 3638-5961, S6a leaves, S6b helpers 6815-8355, S6b leaves, MERGER note 8500, `circleComp_bijective` 8505, `circleEquiv` 8519), `section Assembly` 8525-8543 (`recordIso` 8530, `sweep_proof` 8540), `end` 8545, `end U8R` 8547, blank 8548 | **merged L14568-16708 → delta 44-2184 (offset −14524)**; merged **L16709-16718 deleted** (§3) and replaced by the 3 lines 2185-2187 (2-line note + blank); **merged L16719-23079 → delta 2188-8548 (offset −14531)** |
| **8549-8555** | the leaf **`represent`**: docstring 8549-8551, `theorem represent (F : SmoothFront) : ∃ W : OWord,` **8552**-8554, body `U8R.represent_of_sweepStatement F (U8R.sweep_proof F)` 8555 | merged L23080-23086 (offset −14531), byte-identical |
| 8557, 8559 | `end Leaves`, `end FrontRows` | = merged L23088, 23248 |
| 8561 | `/-! ## Statement of row 76 … -/` | new |
| **8563-8578** (+ blank 8579) | **`structure NgCommutationClauses : Prop where`** with its 9 fields | `Skeleton_W2.lean` **L57-73** (offset +8506), **byte-identical** — `cmp` of the extracted ranges (`/tmp/w2sdelta/struct_delta.txt` vs `struct_skel.txt`) reports no difference.  Placed after `end FrontRows` and BEFORE `open FrontRows`, so it elaborates in the same context as in the skeleton (`namespace SM`, the two `open`s, nothing from `FrontRows` opened) |
| 8580, 8582 | `open FrontRows`, `/-! ## Assembly of row 76 -/` | = merged L23250; new heading |
| **8584-8598** (+ blank 8599) | docstring `/-- **ng:commutation** (row 76), assembled. -/` 8584; **`theorem ng_commutation : NgCommutationClauses where`** **8585**-8598 (`represent := represent` at 8598) | merged L23254-23269 (offset −14670), **byte-identical** (`cmp` `/tmp/w2sdelta/ng_delta.txt` vs `ng_merged.txt`) |
| 8600 | `end SM` | = merged L23404 |

Helpers cited by `ng_commutation` and where they are: `comm_counts` (`FrontRowsW2` L907), `P_comm` (L14518), `deform_downCount`
(L13323), `deform_writhe` (L13328), `deform_P` (L13333) — all in `SM.FrontRowsW2`, reached through `open FrontRows`; `represent`
(delta L8552).  `represent` cites `U8R.represent_of_sweepStatement` (`FrontRowsW2` L13891) and `U8R.sweep_proof` (delta L8540).
Nothing else had to be added: the delta contains exactly the sweep block, `represent`, and the two row-76 declarations.

**Verbatim check** (done by `delta_w2s.py`, asserted): delta L44-8548 with L2185-2187 removed == merged L14568-16708 ++ L16719-23079;
delta L8549-8555 == merged L23080-23086; delta L8563-8579 == skeleton L57-73; delta L8584-8599 == merged L23254-23269.  The three
`/-! MERGER … -/` relocation notes of the merged file (delta L603, 1157, 3319, 8500) are kept — the relocations they describe are
load-bearing (W3S_MERGE_REPORT §2).

## 3. Removed: the two false leaves (merged L16709-16718, 10 lines)

| merged lines | text | why |
|---|---|---|
| 16709-16711 | docstring `/-- LEAF (S1): a continuation carries the bit of its entry … -/` | — |
| 16712-16713 | `theorem dirBit_of_cont_before {q : Param F.c} {a : Param F.c × ℕ} (ha : ¬ F.IsLeftCusp a.1) (hj : …) (h : Cont F q a) : dirBit F q = entryBit F (beforeBits F) a := sorry` | **false as stated** (W3S_MERGE_REPORT §4: `q` may itself be a cusp, where `xvel = 0`); consumed by nothing |
| 16714 | blank | — |
| 16715 | docstring `/-- LEAF (S1): the same after the x-value … -/` | — |
| 16716-16717 | `theorem dirBit_of_cont_after … := sorry` | idem |
| 16718 | blank | — |

Replaced by (delta L2185-2187): a 2-line `/-! … removed: false as stated … replaced by the proved s1b_dirBit_of_cont_before /
s1b_dirBit_of_cont_after (extra hypothesis ¬ F.IsCusp q) -/` note and a blank line.  The corrected leaves are in the module
(`s1b_dirBit_of_cont_before` L2072, `s1b_dirBit_of_cont_after` L2103, both `[propext, Classical.choice, Quot.sound]`).  That nothing
consumed the removed pair is confirmed by the compile (0 errors after deletion) and by the axioms of `represent`/`sweep_proof`.
Nothing else was removed or changed; the word "sorry" does not occur in the module.

## 4. Statement declarations of row 76 in the delta (FrontRows_W2S_Delta.lean line numbers)

| declaration | kind | delta line | notes |
|---|---|---|---|
| **`SM.NgCommutationClauses`** | structure (row 76 statement) | **8563**-8578 | fields `comm_D`, `comm_w`, `comm_d`, `comm_B`, `deform_D`, `deform_w`, `deform_d`, `deform_B`, `represent`; byte-identical to Skeleton_W2 L57-72 |
| **`SM.ng_commutation`** | theorem `: NgCommutationClauses` | docstring 8584, **8585**-8598 | byte-identical to merged L23254-23268 |
| **`SM.FrontRows.represent`** | theorem (the U8R leaf) | docstring 8549-8551, **8552**-8555 | byte-identical to merged L23080-23086 |
| `SM.FrontRows.U8R.sweep_proof` | theorem `: SweepStatement F` | 8540 | consumed by `represent` |
| `SM.FrontRows.U8R.recordIso` | def | 8530 | consumed by `sweep_proof` |

(The executor's port prepends one "Ported …" comment line, as it did for `FrontRowsW2`; every number above then shifts by +1 in
`work/lean/SM/FrontRowsW2S.lean`.)

## 5. Name-clash scan (namespace-aware)

`work/drafts/frontrows/clash_scan_w2s.py` (= `clash_scan_w2.py` pointed at the delta; log `/tmp/w2sdelta/clash_scan.log`, full list
`/tmp/w2sdelta/delta_decls.txt`): builds the fully-qualified name (tracking `namespace`/`section`/`end`, skipping comments) of every
top-level declaration of the delta (598, all distinct — no duplicate inside the file) and of every `.lean` under `work/lean` outside
`.lake` (663 files, **including `SM/FrontRowsW2.lean`**, 1,116 declarations), and intersects.  **Result: 0 clashes**; an explicit
delta-vs-`FrontRowsW2.lean` intersection is also empty.  Namespaces used: `SM.FrontRows.U8R` (595: the 450 unit-prefixed helpers
`s1a_`/`s1b_`/`s2_`/`s3s5_`/`s4a_`/`s4b_`/`s6a_`/`s6b_`, the SweepDefs/S5/S6 definitions, the 52 proved leaves, `recordIso`,
`sweep_proof`), `SM.FrontRows` (1), `SM` (2).  Secondary short-name check: `ng_commutation`, `NgCommutationClauses`, `represent`,
`sweep_proof`, `oword`, `word_closed`, `circleEquiv`, `slotAt`, `events`, `cutBefore`, `cutAfter`, `hybridCut` are declared nowhere in
`work/lean`; `recordIso` exists in three other namespaces (`SM.SpatialLink.HeightMarking`, `SM.SpatialLink.CleanCuspSmoothing`,
`SM.SmoothFront.Marking`) — different namespaces, no clash, and the merged file already compiled with them in scope.  The compile
confirms independently (Lean rejects a duplicate declaration).

## 6. Recipe for the FINAL delta (rows 77-80 and 83; `import SM.FrontRowsW2S`)

The final module (suggested name `FrontRows_W3F_Delta.lean` → `work/lean/SM/FrontRowsW3.lean`) is written once the L-geo lane's
`Skeleton_W3.lean` (= `Skeleton_W2.lean` + the U5/U6 hunks in the region Skeleton_W2 L11085-11128) has all four front-move leaves
proved.  It `import SM.FrontRowsW2S` (which transitively imports `SM.FrontRowsW2` and everything else) and contains, in this order,
with the SAME preamble (`namespace SM`, `open SM.FrontWord SM.Link`, `open scoped ContDiff`):

| # | content | source (verbatim) | scope |
|---|---|---|---|
| 1 | the five row statements `NgFrontIClauses`, `NgFrontIIClauses`, `NgFrontIIIClauses`, `NgDeletionsClauses`, `NgLocalFrontBoundClauses` | Skeleton_W2 L74-102 and L119-122 (W2_CLEAN_REPORT §3 rows 2-6) | `namespace SM`, before any `open FrontRows` |
| 2 | `namespace FrontRows`, `section Leaves`; the L-geo docstring (Skeleton_W2 L11085-11092, optional), the **U5 block** + `typeIII_site`, the **U6 block** + `typeII_move`, `typeI_move`, `crossedCusp_move` | the hunks of `diff Skeleton_W2.lean Skeleton_W3.lean` (all in L11085-11128; today `W3_U5.lean` 11092a/11101c and `W3_U6.lean` 11102a/11119c/11128c) — the blocks carry their own `namespace U5`/`U6`, `open`s and `noncomputable section`; they depend only on U1-U4 (`FrontRowsW2`) | `SM.FrontRows`, `SM.FrontRows.U5/U6` |
| 3 | `end Leaves`; the four consumers `P_typeIII`, `P_typeII`, `P_typeI`, `P_crossedCusp` | Skeleton_W2 L14619-14643 | `namespace FrontRows` |
| 4 | `end FrontRows`, `open FrontRows`; rows 77-80 `ng_front_I`, `ng_front_II`, `ng_front_III`, `ng_deletions` | Skeleton_W2 L14757-14804 (= merged L23270-23317) | `namespace SM` |
| 5 | `namespace FrontRows`, the row-83 docstring, `certificate_laws`, `word_bound`, `end FrontRows` | Skeleton_W2 L14842-14877 | `SM.FrontRows` |
| 6 | row 83 `ng_local_front_bound`, `end SM` | Skeleton_W2 L14878-14890 | `namespace SM` |

It must **NOT** re-declare anything from `SM.FrontRowsW2S`: `NgCommutationClauses`, `ng_commutation`, `represent`, and all 595
`SM.FrontRows.U8R` sweep declarations (`SweepDefs` … `sweep_proof`; regenerate the list with `python3 clash_scan_w2s.py` →
`/tmp/w2sdelta/delta_decls.txt`), nor anything from `SM.FrontRowsW2` (W2_CLEAN_REPORT §3 "must NOT be re-declared" list).  Name
resolution is unchanged: inside `namespace SM.FrontRows`, `certificate_laws` reaches `ng_commutation` (= `SM.ng_commutation`) and
`ng_local_front_bound` reaches `ng_commutation.represent` exactly as in the merged file.  Expected checks: `grep -c -i sorry` = 0;
0 errors; `#print axioms` on a `/tmp` copy — `SM.ng_front_I/II/III`, `SM.ng_deletions`: `[propext, Classical.choice, Quot.sound, SM.lp_lm]`;
`SM.FrontRows.certificate_laws`: the same; `SM.ng_local_front_bound`: `[propext, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]`
(`ng_finite_word` is the accepted literature interface consumed by `word_bound`); clash scan against `work/lean` including
`SM/FrontRowsW2.lean` and `SM/FrontRowsW2S.lean` = 0.  Run the same `delta_w2s.py`-style anchored assembly so every range is verified.

## 7. Files

- `work/drafts/frontrows/FrontRows_W2S_Delta.lean` — the module (8,600 lines).
- `work/drafts/frontrows/delta_w2s.py` — regenerates it from `W3S_Merged.lean` + `Skeleton_W2.lean` (anchored; byte-identity asserted) and writes the axiom probe.
- `work/drafts/frontrows/clash_scan_w2s.py` — the namespace-aware clash scan (§5).
- `/tmp/w2sdelta/` — `compile_delta.log`, `compile_ax.log`, `W2S_ax.lean`, `clash_scan.log`, `delta_decls.txt`, the four `cmp` extracts (ephemeral).
