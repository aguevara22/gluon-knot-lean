# W3S_MERGE_REPORT — sweep lane of the front certificate rows, wave 3 merge (S1a + S1b + S2 + S3S5 + S4a + S4b + S6a + S6b)

2026-09-14, merger for the SWEEP lane.  Inputs: `W3_U8R_Skeleton.lean` (15,586 lines, 58 sorries = 54 sweep leaves of
`SM.FrontRows.U8R` + the 4 front-move leaves of the L-geo lane) and the eight unit files `W3S_{S1a,S1b,S2,S3S5,S4a,S4b,S6a,S6b}.lean`
with their reports.  Output: **`work/drafts/frontrows/W3S_Merged.lean`** (23,404 lines), produced by
**`work/drafts/frontrows/mergeS.py`** (rerunnable; it re-derives every hunk from `diff W3_U8R_Skeleton.lean W3S_<u>.lean`,
classifies it, aborts on anything that is not a helper block / a leaf body / one of the three known relocations, assembles,
and verifies the output).  Scratch: `/tmp/mergeS/` (probe copy `W3S_ax.lean`, logs `compile.log`, `ax.log`).
Nothing under `work/lean` was touched; no `lake build`.

## 1. Result

| item | value |
|---|---|
| file | `work/drafts/frontrows/W3S_Merged.lean`, **23,404 lines** (skeleton 15,586; `Skeleton_W2.lean` 14,891) |
| `grep -c sorry` | **6** (skeleton: 58) = the 4 front-move leaves of the L-geo lane (`typeIII_site` L11101, `typeII_move` L11111, `typeI_move` L11119, `crossedCusp_move` L11128, untouched) + the 2 sweep leaves `dirBit_of_cont_before` (L16713), `dirBit_of_cont_after` (L16717), which are FALSE as stated (§4) |
| sweep leaves | **52 of 54 proved**, all 52 sorry-free (`[propext, Classical.choice, Quot.sound]`); S1a 8/8, S1b 6/8, S2 5/5, S3S5 5/5, S4a 9/9, S4b 8/8, S6a 6/6, S6b 5/5 |
| compile (`cd work/lean && lake env lean ../drafts/frontrows/W3S_Merged.lean`) | **exit 0, 0 errors**, 112 s wall on the loaded pod (load ≈ 30); log `/tmp/mergeS/compile.log` |
| warnings | 61 total: 6 × ``declaration uses `sorry` `` (the six leaves above); the rest (55) were all already present in the unit files / skeleton — 2 × "automatically included section variable" (W2 U8R block, L13451/13472), 7 × "Variable name … not explicitly referenced" (L14137, 14256, 14793-14794 skeleton; L17364/17390 S4a's frozen `hk`; L19474 S6a), 8 × unused simp argument (S6a/S6b), 40 × deprecated `if_pos`/`if_neg` (S6a L20292-20416, S6b L21757-22701).  **Nothing new from the merge.** |
| **`SM.FrontRows.represent`** (the U8R leaf) | **`[propext, Classical.choice, Quot.sound]` — sorry-free** |
| **`SM.FrontRows.U8R.sweep_proof`**, `U8R.recordIso` | `[propext, Classical.choice, Quot.sound]` — sorry-free |
| **row 76 `SM.ng_commutation`** | **`[propext, Classical.choice, Quot.sound, SM.lp_lm]` — CLOSED** (`lp_lm` = the accepted literature interface reached through `P`; no `sorryAx`) |
| row 83 `SM.ng_local_front_bound` | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]` — `sorryAx` ONLY through `certificate_laws` (`[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]`), i.e. through the four L-geo leaves of the OTHER lane; the sweep side (`ng_commutation.represent`) no longer contributes any `sorryAx` |
| rows 77-80 | unchanged from wave 2: `sorryAx` through `P_typeI/II/III`, `P_crossedCusp` (L-geo lane) |
| rows 81, 82 | unchanged, closed since wave 2 |
| clashes | none (450 helper declarations, all unit-prefixed, none declared twice, none in `work/lean`, none elsewhere in the file — §6) |
| relocations | 3, all verbatim and load-bearing (§2): S2/S3 leaves before the S1b block; `word_closed`+`oword`+`oword_letters` after `run_take_eq_hybrid`; `circleComp_bijective`+`circleEquiv` after `ΦFun_cycNext` |

## 2. Verification of the units (task step 1)

`diff W3_U8R_Skeleton.lean W3S_<u>.lean`, hunk by hunk (skeleton line numbers).  `mergeS.py` requires, for every hunk:
a **`c` hunk** replaces only `:= sorry` lines of leaves of THAT unit — the first line of the replacement is the byte-identical
statement tail with `sorry` removed, the replacement contains no `sorry` and no top-level item, and any other skeleton
line inside a fused hunk (blank separators) reappears verbatim; an **`a` hunk** is the unit's single block
`/-! ### <u> helpers -/ section <u>Helpers … end <u>Helpers` (no `sorry`, no `import`/`set_option`/`attribute`, every
declared name carries the prefix `<u>_`); a **`d` hunk** is allowed only for the two known relocations and its text must be
re-inserted verbatim (checked by a sub-diff).  All eight units pass; no statement, definition, name or docstring changed.

| unit | hunks (skeleton lines) | classification | leaves proved |
|---|---|---|---|
| S1a | `14866a` (+75: S1a helpers, 8 decls); `c` at 14872, 14877, 14883, 14886, 14888, 14891, 14901, 14908 | block + 8 bodies | 8/8 |
| S1b | `14910,14950c14910,14912` (the S1b leaves replaced by a 3-line `/-! … -/` relocation note); `14993a14956,16056` (S1b helpers, 976 lines / 54 decls, followed by the S1b leaves re-inserted verbatim with 6 bodies) | **relocation**: the S2/S3 leaves (skeleton 14952-14994) are common text and therefore precede the S1b block in the unit file; the S1b block cites them (`cusp_arm_sign`, `leftCusp_x_local`, `rightCusp_x_local`, `leftCusp_arms`, `rightCusp_arms`, `cross_height_order`) | 6/8 — `dirBit_of_cont_before`, `dirBit_of_cont_after` left `sorry` (FALSE as stated, §4) |
| S2 | `14953a` (+251: S2 helpers, 18 decls); `c` at 14960, 14966, 14971, 14977, 14982 | block + 5 bodies | 5/5 |
| S3S5 | `14983a` (+196: S3S5 helpers, 10 decls); `c` at 14993 (S3), 15106, 15113, 15116, 15122 (S5) | block + 5 bodies | 5/5 |
| S4a | `14996a` (+456: S4a helpers, 31 decls); `c` at 14999, 15003, 15006, 15009, 15014, 15022, 15027, 15032, 15037 | block + 9 bodies | 9/9 |
| S4b | `14849,14857d` (`word_closed`/`oword`/`oword_letters` removed from `section SweepDefs`); `15038a` (+375: S4b helpers, 40 decls); `c` at 15042, 15045, 15051 (this hunk = the body of `run_take_eq_hybrid` + the 9 removed lines re-inserted verbatim with `word_closed` proved), 15054, 15057, 15062, 15067 | block + 8 bodies + **relocation** (`word_closed` needs `run_take_eq_hybrid`, `step_hybrid`, `hybridCutStrict_eq_cutAfter`, `cutAfter_last`, all declared later) | 8/8 |
| S6a | `15158a` (+2,327: S6a helpers, 170 decls); `c` at 15161, 15169, 15178, 15187, 15198, 15206 | block + 6 bodies | 6/6 |
| S6b | `15151,15158d` (`circleComp_bijective` docstring/statement + `circleEquiv` removed); `15207a` (+1,543: S6b helpers, 119 decls); `c` at 15215, 15220, 15224, 15232 (this hunk = the body of `ΦFun_cycNext` + the 8 removed lines re-inserted verbatim with `circleComp_bijective` proved) | block + 5 bodies + **relocation** (`circleComp_bijective` needs `slotAt`, the jump leaves, `path_cusps`, `exists_cuspVertex_sameCycle`) | 5/5 |

Notes on the relocations (all three are forced: Lean has no forward references, and the skeleton stated these leaves
before the leaves their proofs consume; PLAN §4 already lists "S1 depends on S2, S3"):
- Nothing declared between the old and new positions uses the moved declarations: no helper block references
  `word_closed`/`oword`/`oword_letters` or `circleComp_bijective`/`circleEquiv` (grepped: S1a, S2, S3S5, S4a, S4b, S6a,
  S6b blocks — zero hits); the first consumers of `word_closed`/`oword` after the new position are `word_ne_nil` and `ΦFun`
  (S5), the only consumer of `circleEquiv` is `recordIso` (Assembly).  Both sections `SweepDefs` and `SweepLeaves` carry
  `variable (F : SmoothFront)`, so `word_closed`, `oword`, `oword_letters` elaborate to the same constants and types.
- The S1b relocation note of the unit file was NOT adopted (it is unit-local prose); `W3S_Merged.lean` carries four
  one-line `/-! MERGER … -/` notes at the four relocation points instead (lines 15127, 15681, 17850, 23031).

Not adopted / violations: **none**.  The only non-body, non-block text in any unit is the three relocations above, all verbatim.

## 3. Layout of `W3S_Merged.lean` (the sweep block; everything before line 14567 and after 23088 is `Skeleton_W2.lean` unchanged)

`diff Skeleton_W2.lean W3S_Merged.lean` = exactly two hunks: **`14567a14568,23079`** (the sweep block
`/-! ### U8R sweep … -/ namespace U8R … end U8R`) and **`14573c23085,23086`** (`represent … := sorry` →
`:=\n  U8R.represent_of_sweepStatement F (U8R.sweep_proof F)`).  The `import` lines are identical to the skeleton's.

| lines | content |
|---|---|
| 14568-14596 | header docstring, `namespace U8R`, `open …`, `noncomputable section` (skeleton) |
| 14597-14850 | `section SweepDefs`: all S1/S4 definitions (skeleton, minus the moved `word_closed` block) |
| 14852-17954 | `section SweepLeaves` (`variable (F : SmoothFront)`): |
| 14858-14931 | `S1a helpers` (74 lines) |
| 14933-15125 | the 8 S1a leaves, all proved (`fibreListBefore_eq_of` 14936 … `exists_eta_fibre_near` 15081) |
| 15127 | MERGER note; **15129-15436 the S2 leaves** (skeleton 14952-14983) with `S2 helpers` 15131-15380 in front of them (`cusp_arm_sign` 15386 … `rightCusp_arms` 15436) |
| 15443-15637 | `S3S5 helpers`; **15639-15679 the S3 leaf** `cross_height_order` (15645), proved |
| 15681 | MERGER note; 15683-16658 `S1b helpers` (976 lines) |
| 16660-16780 | the 8 S1b leaves (skeleton 14910-14950): `entriesBefore_left_limit` 16664, `entriesAfter_right_limit`, **`dirBit_of_cont_before` 16712 `sorry`**, **`dirBit_of_cont_after` 16716 `sorry`**, `cutBefore_left_limit`, `cutAfter_right_limit`, `cutAfter_eq_cutBefore_of_gap`, `posAt_const_of_arc` 16772 |
| 16782-17238 | `#### S4 leaves` header, `S4a helpers` (455 lines) |
| 17240-17413 | the 9 S4a leaves (`evKey_injective` 17242 … `hybridCut_eq_cutBefore` 17390), all proved |
| 17415-17788 | `S4b helpers` (374 lines) |
| 17790-17848 | `cutBefore_first` 17793, `cutAfter_last`, `run_take_eq_hybrid` 17835 |
| 17850-17872 | MERGER note; **`word_closed` 17855 (proved), `oword` 17870, `oword_letters`** (skeleton 14849-14857, relocated) |
| 17874-17952 | `word_ne_nil`, `cuspCount_eq`, `downCountSyn_eq`, `cut_word_colAt` 17910 |
| 17956-18141 | `section SlotMap` (S5): `crossOf`, `ΦFun`, `ΦSub_bijective` 17991, `occEquiv`, `ΦFun_partner`, `isDesc_ΦFun`, `σsgn_ΦFun` 18085 — all proved |
| 18143-23052 | `section Traversal` (S6): `cuspVertex`, `someCuspOn`, `circleComp`; `S6a helpers` 18168-20492 (2,325 lines); the 6 S6a leaves `isSlot_slotAt` 20495 … `path_no_occ` 21226; `S6b helpers` 21345-22886 (1,542 lines); `path_cusps` 22890, `exists_cuspVertex_sameCycle`, `slotComp_ΦFun`, `ΦFun_cycNext` 22967; MERGER note 23031; **`circleComp_bijective` 23036 (proved), `circleEquiv` 23050** (skeleton 15151-15158, relocated) |
| 23056-23074 | `section Assembly`: `recordIso` 23061, `sweep_proof` 23071 (skeleton, proved from the leaves) |
| 23078 | `end U8R`; 23083 `represent` (proved: `U8R.represent_of_sweepStatement F (U8R.sweep_proof F)`); 23088 `end Leaves` |

## 4. Remaining sweep leaves (2 of 54) — and why they stay `sorry`

| leaf | line | status |
|---|---|---|
| `dirBit_of_cont_before` | 16712 | **FALSE as stated** (S1b report §3; re-checked by the merger below).  Corrected form proved in the file: `s1b_dirBit_of_cont_before (hq : ¬ F.IsCusp q) (hj) (h : Cont F q a)` (L16596). |
| `dirBit_of_cont_after` | 16716 | **FALSE as stated**; corrected form `s1b_dirBit_of_cont_after (hq : ¬ F.IsCusp q) …` (L16627). |

The frozen statement: `(ha : ¬ F.IsLeftCusp a.1) (hj : a.2 < (beforeBits F a.1).length) (h : Cont F q a) :
dirBit F q = entryBit F (beforeBits F) a`.  `Cont F q a` (L14747) says only: `q` is on `a`'s circle, its lifted parameter
`s ≠ a.1.2`, **no cusp strictly between** `s` and `a.1.2`, and the arm clause when `a.1` is a cusp.  It does not exclude `q`
itself being a cusp.  Take `a.1 = (i, t)` regular with `0 < xvel F i t` and `a.2 = 0` (so `beforeBits F a.1 = [true]`,
`hj`, `ha` hold, `entryBit = true`), and `q := (i, c)` with `c` the first cusp parameter after `t` (`exists_arc_mem` puts `t`
on an arc `[c₀, arcEnd c₀]`, `not_isCusp_of_mem_arc` gives the cusp-free clause, `isCusp_arcEnd` makes `c := arcEnd c₀` a
cusp).  Then `Cont F q a` holds with `s := c`, but `dirBit F q = decide (0 < xvel F i c) = false` because `xvel = 0` at a
cusp (`isCusp_iff_xvel_eq_zero`).  Every front has such a configuration (every circle has a right cusp, at which `x` has a
strict local max, so `xvel > 0` just before it), so the statement fails for every `F`; no proof is possible and none was
attempted beyond confirming this.  Neither leaf is consumed by any other leaf or by the assembly: `represent`,
`sweep_proof`, `recordIso` are sorry-free (§5).  If the architect wants them closed, amend the statements by adding
`(hq : ¬ F.IsCusp q)` (and the redundant `ha` may be dropped); the bodies are then
`s1b_dirBit_of_cont_before F hq hj h` / `s1b_dirBit_of_cont_after F hq hj h`.

The other four `sorry`s of the file are the L-geo lane's front-move leaves: `typeIII_site` (L11101), `typeII_move`
(L11111), `typeI_move` (L11119), `crossedCusp_move` (L11128) — untouched, exactly as in `Skeleton_W2.lean`.

## 5. `#print axioms` (probe `/tmp/mergeS/W3S_ax.lean` = `W3S_Merged.lean` + 66 `#print axioms` lines; log `/tmp/mergeS/ax.log`)

| declaration | what | axioms | status |
|---|---|---|---|
| `SM.FrontRows.represent` | the U8R leaf (row 76 field `represent`) | `[propext, Classical.choice, Quot.sound]` | **sorry-free** |
| `SM.FrontRows.U8R.sweep_proof` | the sweep statement | `[propext, Classical.choice, Quot.sound]` | **sorry-free** |
| `SM.FrontRows.U8R.recordIso` | the record isomorphism | `[propext, Classical.choice, Quot.sound]` | **sorry-free** |
| `SM.ng_commutation` | row 76 | `[propext, Classical.choice, Quot.sound, SM.lp_lm]` | **CLOSED by this merge** (was `sorryAx` through `represent` in `Skeleton_W2.lean`) |
| `SM.ng_front_I` | row 77 | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]` | open — L-geo lane (unchanged from wave 2) |
| `SM.ng_front_II` | row 78 | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]` | open — L-geo lane (unchanged from wave 2) |
| `SM.ng_front_III` | row 79 | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]` | open — L-geo lane (unchanged from wave 2) |
| `SM.ng_deletions` | row 80 | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]` | open — L-geo lane (unchanged from wave 2) |
| `SM.ng_circle` | row 81 | `[propext, Classical.choice, Quot.sound, SM.lp_lm]` | **sorry-free** |
| `SM.ng_cusp_skein` | row 82 | `[propext, Classical.choice, Quot.sound, SM.lp_lm]` | **sorry-free** |
| `SM.FrontRows.certificate_laws` | glue for row 83 | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]` | open — L-geo lane (unchanged from wave 2) |
| `SM.ng_local_front_bound` | row 83 | `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]` | open — `sorryAx` only via `certificate_laws` ← the four L-geo leaves (`typeIII_site`, `typeII_move`, `typeI_move`, `crossedCusp_move`) of the other lane; `SM.ng_finite_word` is the accepted literature interface consumed by `word_bound`.  The sweep contributes nothing to its `sorryAx` any more: `ng_commutation` (whose field `represent` it opens with) is sorry-free. |

The 54 sweep leaves: **52 are `[propext, Classical.choice, Quot.sound]`** (no `sorryAx`); the 2 with `sorryAx` are exactly the two unproved (false) leaves ['dirBit_of_cont_before', 'dirBit_of_cont_after'].  No proved leaf depends on them (they are consumed by nothing — `represent` is sorry-free).

## 6. Name-clash scan (task step 5)

Scanned the 450 declarations of the eight helper blocks (`mergeS.py`'s `DECL_RE`: theorem/lemma/def/abbrev/instance/structure/
inductive/class/opaque/axiom at column 0, `@[…]`/`private`/`protected`/`noncomputable` prefixes allowed; no anonymous instances):
- **against each other**: no name declared twice; every name carries its unit prefix (`s1a_` 8, `s1b_` 54, `s2_` 18,
  `s3s5_` 10, `s4a_` 31, `s4b_` 40, `s6a_` 170, `s6b_` 119);
- **against the rest of `W3S_Merged.lean`** (skeleton + W2 blocks): no helper name is declared elsewhere in the file;
- **against `work/lean`** (every `.lean` under `work/lean` outside `.lake`, 328 modules): no helper name is declared there,
  and no helper name is the last component of a dotted library name (so no dot-notation ambiguity inside
  `namespace SM.FrontRows.U8R`).
- The compile confirms it independently: Lean rejects a duplicate declaration, and the merged file has 0 errors.

**Clashes: none.  No rename needed.**

**Duplicated helpers (identical statement, different names — reported, NOT folded).**  17 statement texts occur in two
or more blocks under different prefixed names, e.g. `xOf F i (t + n) = xOf F i t` (`s1b_xOf_add_int` = `s6a_xOf_add_int`
= `s6b_xOf_add_int`), `evX F e ∈ singX F` (`s1b_`/`s4b_`/`s6a_evX_mem_singX`), `beforeBits F p = [dirBit F p]` for a regular
point (`s1b_bits_regular_before` = `s4a_beforeBits_of_regular`), `ht F q ≤ ht F p` from `beforeLE`/`afterLE` (four/three
copies), `eventAt F k = (events F)[k]` (three), `(letterOf F e).idx = posOf F e` (three), `F.eval (i, Int.fract t) = F.eval (i, t)`
(`s4b_eval_fract` = `s6a_eval_rep`), `evZ F e = colZ F (evIdx F e)`, `∃ e, evX F e = x` for `x ∈ singX F`,
`(entriesOf F bits L).length = (L.flatMap bits).length`, `¬ F.IsCusp p.1` for an occurrence, and the S4a/S4b/S3S5 cut-split
lemmas (`s4a_before_split_le` = `s4b_filter_le_split`; `s3s5_filter_height_eq` = `s4a_before_filter_cross`).  They are not
*identical declarations* (names differ, proofs differ), folding them means editing the consuming proofs of another unit,
and they cost nothing (0 errors, ~4 % of the helper lines).  De-duplication of byte-identical helpers: nothing to do —
there are none.  If a clean-up pass is wanted later, the list above is the worklist (the `s6b_` copy is the most complete
in each case).

## 7. The FINAL merge with the other lane (`Skeleton_W3.lean` = `Skeleton_W2.lean` + the U5/U6 hunks)

Both lane outputs are `Skeleton_W2.lean` plus disjoint, non-adjacent edits, so the final file is the **union of the two
hunk sets** applied to `Skeleton_W2.lean` — order-independent.

- **This lane** (`W3S_Merged.lean`): `diff Skeleton_W2.lean W3S_Merged.lean` = `14567a14568,23079` (the sweep block,
  inserted right before the docstring of `represent`) + `14573c23085,23086` (`represent` proved).  Lines 1-14566 of
  `W3S_Merged.lean` are byte-identical to lines 1-14566 of `Skeleton_W2.lean`; lines 23087-23404 = `Skeleton_W2.lean` 14574-14891.
- **The other lane** (as of the unit files present now; `Skeleton_W3.lean` does not exist yet in `work/drafts/frontrows/`):
  `diff Skeleton_W2.lean W3_U5.lean` = `11092a11093,13042` (U5 block) + `11101c13051,13065` (`typeIII_site`);
  `diff Skeleton_W2.lean W3_U6.lean` = `11102a11103,17036` (U6 block) + `11119c17053` (`typeI_move`) + `11128c17062`
  (`crossedCusp_move`) — `typeII_move` (L11111) is still `sorry` in `W3_U6.lean` at the time of writing.  Whatever
  `Skeleton_W3.lean` finally contains, its hunks all live in the L-geo region **11085-11128 of `Skeleton_W2.lean`**,
  i.e. strictly before our insertion point 14567.

**Recipe (either direction works; A is the simplest).**

A. Apply the L-geo hunks to our file — they sit before line 14567, where the two files coincide, so the L-geo diff applies
at its own `Skeleton_W2` line numbers without offset:
```
cd work/drafts/frontrows
diff Skeleton_W2.lean Skeleton_W3.lean > /tmp/lgeo.diff        # normal diff; all hunks at lines 11085-11128
cp W3S_Merged.lean Skeleton_W3_FINAL.lean
patch Skeleton_W3_FINAL.lean /tmp/lgeo.diff                      # must report every hunk applied cleanly, no offset/fuzz
```
B. Symmetrically, `diff Skeleton_W2.lean W3S_Merged.lean > /tmp/sweep.diff; cp Skeleton_W3.lean Skeleton_W3_FINAL.lean;
patch Skeleton_W3_FINAL.lean /tmp/sweep.diff` — here `patch` WILL report an offset (= the number of lines U5/U6 inserted
before 14567), which is expected and harmless because the hunk context is unchanged; prefer A to avoid the ambiguity.
C. Or extend `merge2.py`: set `BASE = Skeleton_W2.lean`, `UNITS = ["W3S_Merged", "Skeleton_W3"]`, `OUT = Skeleton_W3_FINAL.lean`
— its overlap check will confirm the hunk sets are disjoint and it applies them bottom-up with verbatim verification.

**Verify the final file:**
1. `diff Skeleton_W3.lean Skeleton_W3_FINAL.lean` shows exactly our two hunks (`14567a` shifted by the U5/U6 insertion size,
   `14573c`), and `diff W3S_Merged.lean Skeleton_W3_FINAL.lean` shows exactly the L-geo hunks — nothing else.
2. `grep -c sorry Skeleton_W3_FINAL.lean` = 2 (the two false `dirBit_of_cont_*` leaves) + however many L-geo leaves
   `Skeleton_W3.lean` leaves open (0 if U5/U6 close all four).
3. `cd work/lean && lake env lean ../drafts/frontrows/Skeleton_W3_FINAL.lean` — 0 errors (expect ~3-5 min on the loaded
   machine; the sweep block alone is 8.5k lines).  Namespaces cannot clash: U5/U6 live in `SM.FrontRows.U5`/`.U6`, the sweep
   in `SM.FrontRows.U8R` with unit-prefixed helper names.
4. `#print axioms` on a `/tmp` copy for `SM.ng_commutation` (row 76; must be `[propext, Classical.choice, Quot.sound, SM.lp_lm]`
   — it is already so in `W3S_Merged.lean`), `SM.ng_front_I/II/III`, `SM.ng_deletions` (closed by U5/U6) and
   `SM.ng_local_front_bound` (row 83; sorry-free iff all four L-geo leaves are proved — the sweep side is done).
5. Then the usual W2-clean pass (`clean_w2.py`-style: drop the four `/-! MERGER … -/` notes if unwanted, keep the
   relocations — they are load-bearing) before porting into `work/lean`.

## 8. Notes

- The merged compile carries the warnings the units already had (deprecated `if_pos`/`if_neg` in S6a, a few unused
  simp-args / unused variables, the two pre-existing "automatically included section variable" notes of the W2 U8R block at
  13451/13472); nothing new from the merge.  The exact list is in §1.
- `mergeS.py` fuses nothing and moves nothing beyond the three relocations; it asserts 26 content anchors on the skeleton
  (line numbers + text) so it fails loudly if rerun on a different skeleton.
- Time: merge script + verification ~1 min; full compile of the 23.4k-line file 112 s (probe copy with 66 `#print axioms`: 120 s) on the loaded pod (load ≈ 30).
