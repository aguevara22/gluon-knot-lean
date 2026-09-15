# thm:C-S3 — assembly report

Written 2026-09-14 01:05 UTC / 9:05pm ET by the assembler subagent. Toolchain: Lean v4.34.0-rc2 +
Mathlib pin of `work/lean`; checked with `cd work/lean && lake env lean <file>` only (no `lake build`).

## Result

`work/drafts/cs3/CS3_Assembled.lean` — **2509 lines, zero occurrences of `sorry`** (not even in comments),
compiles with **no errors and no warnings**, wall time **7 s** (the imported `.olean`s were already built).

```
'SM.thm_C_S3' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly]
```
(run on `/tmp/CS3_Assembled_axioms.lean` = the assembled file + `#print axioms SM.thm_C_S3`; 8 s; exit 0).
No `sorryAx`; `SM.lp_lm` / `SM.lp_lm_uniqueness` do not appear. `SM.lit_homfly` is the registered
literature axiom (`work/lean/axiom-policy.json` → `/literature/lit:homfly`).

Sanity check of the checker: replacing the proof of `thm_C_S3` by `exact 0` in a `/tmp` copy produces the
expected type error at line 2493 and exit 1, so a silent pass is excluded.

## Inputs and verification of the unit diffs

`diff -u Skeleton_FINAL.lean U<k>.lean` for k = 1, 2, 3. Every removed line is exactly `  sorry`; no
statement, definition, import, or section line was changed by any unit.

| unit | hunks (skeleton line ranges) | lines added | `sorry` removed | lemmas closed |
|---|---|---|---|---|
| U1 | 82–88, 117–123, 129–135, 226–232 | 409 | 4 (skel. lines 85, 120, 132, 229) | `regular_adjacent_meet`, `edgeSegment_appendVertex_union`, `appendVertex_new_pairs_disjoint`, `Link.single_generic_appendVertex` |
| U2 | 246–256, 259–265, 287–292 (insert only), 307–313 | 546 | 3 (skel. lines 253, 262, 310) | `subdivPt_bijective`, `traversalKey_subdivPt_lt_iff`, `reparam_positiveDiagram_single_appendVertex` |
| U3 | 338–344, 665–670 (insert only), 683–689, 709–715 | 188 | 3 (skel. lines 341, 686, 712) | `exists_appendVertex_of_erase_flat`, `mu_j_unique_edge`, `exists_appendVertex_central` |

Skeleton: 1376 lines, 10 `sorry` lines (line 14 of the skeleton is the word inside the module docstring).
1376 + 409 + 546 + 188 − 10 = 2509. ✓

## How the merge was done

Three patch files (`/tmp/cs3_U{1,2,3}.patch`) applied in order U1, U2, U3 with GNU `patch -u` to one copy
of `Skeleton_FINAL.lean`. All 12 hunks applied with context intact; U2's hunks landed at offset +405 and
U3's at +948 (pure line shifts from the earlier insertions). No rejects. The three regions are disjoint
(U1 ends at skeleton line 232, U2 spans 246–313, U3 starts at 338), so no hunk interleaving was needed.

**De-duplication / renaming: none required.** The helper declarations added by the units have pairwise
distinct names:
- U1: `zero_ne_neg_one_of_three_le`, `neg_two_ne_neg_one_of_three_le`, `det_smul_left`,
  `edgeInterior_appendVertex_{old,last_subset,new_subset,halves_disjoint}`, `adjacent_insertIndex_of_adjacent`,
  `appendVertex_{zero_not_mem_last,last_not_mem_new,tail_off,transverse,no_triple}`.
- U2: `subdivPt_trichotomy`, `subdivPt_{fst,snd}_of_{ne,lt,ge}`, `val_add_one_lt_of_ne_neg_one`,
  `subdivKeyMap` (def) + `subdivKeyMap_strictMono`, `traversalKey_subdivPt`, `neg_one_ne_zero_of_three_le`,
  `remote_insertIndex_of_remote`, `remote_insertIndex_last_of_remote`, `remote_insertedIndex_of_remote`,
  `remote_subdivPt_fst`, `adjacent_subdivPt_fst_of_eq`, `not_remote_subdivPt_of_vertex`,
  `remote_of_remote_subdivPt`, `det_smul_smul_plane`, `edge_appendVertex_subdivPt_fst`,
  `det_edge_subdivPt_pos_iff`, `exists_crossing_overVisit_eq`, and one
  `set_option linter.unusedVariables false in` (kept as in U2).
- U3: `mu_j_unique_edge_ccp`.
Near-misses that are genuinely different lemmas: U1 `zero_ne_neg_one_of_three_le : (0 : ZMod m) ≠ -1` vs
U2 `neg_one_ne_zero_of_three_le : (-1 : ZMod m) ≠ 0`; U1 `det_smul_left` vs U2 `det_smul_smul_plane`.

## Non-unit edits (module docstring only)

Three header lines of the module docstring (lines 6, 14, 15) were updated so the file no longer
describes itself as a skeleton with open `sorry`s: title now `— ASSEMBLED (units U1, U2, U3 merged into
Skeleton_FINAL)`, and "Every lemma of the chain is STATED (the open ones with `sorry`)" became "Every lemma
of the chain is PROVED (units U1, U2, U3 of work/drafts/cs3/ merged in place, statements unchanged)".
No Lean code outside the unit hunks was touched.

## Statement fidelity vs `work/drafts/CS3_statement.lean`

- `structure CS3Data : Prop where … cornerStateSum hn (generic_deleteVertex hn hz hb hc)` (14 lines, 896
  bytes): **byte-identical** (`cmp` on the extracted blocks; assembled lines 2476–2489).
- Row theorem: `theorem thm_C_S3 : CS3Data` identical (assembled line 2493). The statement file continues
  `:= by sorry`; the assembly continues `where flat_law := by …` — only the proof introducer differs.
- Imports differ by design: the statement file imports `SM.FlatCarriersDefs`, `SM.CornerStateSum`; the
  assembly imports `SM.FlatCarriers`, `SM.CX1`, `SM.CChamber`, `SM.GermSides` (as in the skeleton).

## Files

- `work/drafts/cs3/CS3_Assembled.lean` — the deliverable (2509 lines).
- `work/drafts/cs3/ASSEMBLY_REPORT.md` — this file.
- `/tmp/CS3_Assembled_axioms.lean`, `/tmp/cs3_axioms.log`, `/tmp/cs3_compile.log`, `/tmp/cs3_U{1,2,3}.patch` — scratch.
