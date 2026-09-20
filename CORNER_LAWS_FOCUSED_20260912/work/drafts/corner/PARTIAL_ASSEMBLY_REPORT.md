# PARTIAL_ASSEMBLY_REPORT — corner chain, wave-1 partial assembly (2026-09-15 18:10 UTC / 2:10pm ET)

Assembler subagent.  Inputs: the frozen `work/drafts/corner/Statements_FINAL.lean` (764 lines, sha256
`c2e98430…ea52f`) and the twelve returned wave-1 unit files `U_{SGA,SGB,SGC,SGE,SFTA,SFTB,S7B,S7C,S7D,S7G,S7H,S7I}.lean`
with their `U_*_REPORT.md`.  **`U_S7A` is EXCLUDED** (still running; its file is still a byte-identical copy of the
frozen statements, same sha256).  All twelve unit files were present; **`U_SFTA_REPORT.md` is missing** (the unit
file exists and was verified directly, see §1).

Output: **`work/drafts/corner/Partial_Assembled.lean`** (7390 lines, sha256 `85312954…081891`), produced by
`work/drafts/corner/tools/partial_assemble.py`; statement identity checked by `work/drafts/corner/tools/stmt_check.py`.

Check (mandated): `cd work/lean && lake env lean ../drafts/corner/Partial_Assembled.lean` — **0 errors**, 20 s warm
(machine load ≈ 10 on 8 cores), 24 warnings = **10 `declaration uses sorry`** (exactly the 6 open leaves + the 4 §6 row
theorems, §3) + 14 linter/deprecation warnings, all inside the U_SFTA block (§4).  `grep -c sorry Partial_Assembled.lean`
= **12** = 10 sorry bodies + the 2 prose mentions of the frozen file (header line 25, §6 header line 7357).

## 1. Diff audit of the twelve units against Statements_FINAL.lean (task 1)

Method (`tools/partial_assemble.py`): GNU `diff` in normal format, every hunk classified.  A hunk is CLEAN iff it is a
pure insertion (`Na…`: a helper block, or an `import` line inside the import header) or a `c`-hunk whose REMOVED lines
are exactly the `sorry` body of one of the ten leaves of PLAN_FINAL §4 (`  sorry` alone, or `<statement tail> := by` +
`  sorry` replaced by `<statement tail> :=` + a term).  Anything that deletes or changes any other frozen line, or
touches a §6 row theorem's `sorry`, is a VIOLATION and the unit is not adopted.

| unit | PLAN row | hunks vs frozen | removed frozen lines | classification | verdict |
|---|---|---|---|---|---|
| U_SGA | U103-A leaf `sg_isolated_undominated` | `215c215,257` | `  sorry` (line 215) | leaf body, 43 lines | **clean, adopted** |
| U_SGB | U103-B helpers `sgb_` | `216a217,559` | none | helper block, 343 lines | **clean, adopted** |
| U_SGC | U103-C helpers `sgc_` | `216a217,286` | none | helper block, 70 lines | **clean, adopted** |
| U_SGE | U103-E leaf `sg_daughters_rotation` + `sge_` | `236a237,601`, `256c621,647` | `  sorry` (line 256) | helper block 365 lines + leaf body 27 lines | **clean, adopted** |
| U_SFTA | U112-A helpers `sfta_` (no report) | `615a616,2049` | none | helper block, 1434 lines | **clean, adopted** (verified directly: `lake env lean U_SFTA.lean` 0 errors, 18 s, 14 sorry warnings = helper unit; 16 linter/deprecation warnings) |
| U_SFTB | U112-B leaf `sft_mixed` + `sftb_` | `626a627,739`, `634c747,766` | `  sorry` (line 634) | helper block 113 lines + leaf body 20 lines | **clean, adopted** |
| U_S7B | U110-B helpers `s7b_` | `16a17`, `453a455,2168` | none | `import SM.VertexSides` + helper block 1714 lines | **clean, adopted** (import unioned, §2) |
| U_S7C | U110-C helpers `s7c_` | `454a455,1120` | none | helper block, 666 lines | **clean, adopted** |
| U_S7D | U110-D helpers `s7d_` | `454a455,1004` | none | helper block, 550 lines | **clean, adopted** |
| U_S7G | U110-G leaf `s7_universal_extraction` + `s7g_` | `488a489,624`, `493,494c629,630` | line 493 `… := by` → `… :=`, line 494 `  sorry` | helper block 136 lines + one-line term body | **clean, adopted** (normalised, §2) |
| U_S7H | U110-H helpers `s7h_` | `467a468,782` | none | helper block, 315 lines | **clean, adopted** |
| U_S7I | U110-I helpers `s7i_` | `467a468,1299` | none | helper block, 832 lines | **clean, adopted** |

**Violations: none.**  No unit changed a statement, definition, structure, name or docstring; no unit touched a §6 row
theorem or another unit's leaf; no unit's added text contains `sorry`.  Cross-references between units occur only in
docstrings (U_SGC → `sg_daughters_products`, U_SFTB → `sft_mixed`, U_S7C/G/H → `s7_*`, U_S7I → `s7c_*`); no unit's
CODE depends on another unit's helpers, so the blocks are order-independent.

Name-clash scan over the 488 added declarations: every top-level name carries its unit prefix; the unprefixed
names live inside unit namespaces (`s7b_ReturnTransport.*`, `s7b_SupportSplit.*`, `s7b_PivotSplit.*`,
`s7b_SlidingTransport.*`, `sfta_InsertMarkTransport.*`).  The two repeated short names `sameCycle_iff`, `sameCycle_of`
are `s7b_ReturnTransport.…` vs `sfta_InsertMarkTransport.…` — different full names, no clash.  No identical helper
appeared twice, so the de-duplication and rename-on-clash paths of the script were not exercised
(`dedup_dropped = []`, `renamed = []`).  Known REDUNDANCIES with accepted library lemmas NOT among the frozen imports
(different names, no clash; replace at port time if the module is imported): `sftb_markSuccessor_vertex_of_no_crossing`
= `Carrier.markSuccessor_vertex_of_no_crossing` (SM/CS5.lean:30); `s7c_carrierWeight_eq_cornerSelector` =
`carrierWeight_eq_cornerSelector` (SM/CS3.lean:1453).

## 2. Assembly (task 2) — `tools/partial_assemble.py`

`Partial_Assembled.lean` = `Statements_FINAL.lean` with every clean hunk applied:

* the four leaf bodies replaced in place (`sg_isolated_undominated`, `sg_daughters_rotation`, `sft_mixed`,
  `s7_universal_extraction`);
* the eleven helper blocks inserted verbatim and CONTIGUOUSLY at each unit's own anchor (blocks sharing an anchor
  follow in unit order; a blank separator line is added only where two non-blank lines would otherwise touch).
  Verified programmatically: each block occurs as one contiguous slice of the assembled file —

  | block | assembled lines | inside |
  |---|---|---|
  | U_SGB | 260-602 | `section Singleton`, after `sg_isolated_undominated` |
  | U_SGC | 603-672 | idem, before the docstring of `sg_daughters_products` |
  | U_SGE | 693-1057 | `section Singleton`, before the docstring of `sg_daughters_rotation` |
  | U_S7B | 1301-3014 | `section VertexEdge`, before the docstring of `s7_sliding_law_at` |
  | U_S7C | 3016-3681 | idem |
  | U_S7D | 3682-4231 | idem |
  | U_S7H | 4245-4559 | `section VertexEdge`, before the docstring of `s7_bigon_law_at` |
  | U_S7I | 4560-5391 | idem |
  | U_S7G | 5413-5548 | `section VertexEdge`, before the docstring of `s7_universal_extraction` |
  | U_SFTA | 5676-7109 | `section Soft`, before the docstring of `sft_same_sign` |
  | U_SFTB | 7121-7233 | `section Soft`, before the docstring of `sft_mixed` |

  The units' own `section … end`, `namespace … end`, `variable`, `omit [NeZero n] in` wrappers are kept exactly as
  the units wrote them (the frozen file's `attribute [local instance] Classical.propDecidable`, `noncomputable
  section`, `open Link Carrier` / `open SoftDuplication` still enclose everything); no unit added an `open`,
  `attribute` or `set_option` of its own.
* **Import union**: `import SM.VertexSides` (U_S7B; lem:wall-sides (V) is unreachable from the 16 frozen imports and
  is the setup input of the whole sliding branch, U_S7B_REPORT §0) appended after `import SM.GermSides`.  The frozen
  text does not depend on it; the other eleven blocks compile unchanged under the enlarged import set (no
  ambiguity introduced).
* **One normalisation** (the only text in the file not literally from a unit or the frozen file): U_S7G wrote the leaf
  in term mode, `… :=` / `  s7g_extraction_of_skein FH FL FA k hsk`, which changes the frozen line 493 `… := by`.
  The assembler keeps the frozen line and writes the body `  exact s7g_extraction_of_skein FH FL FA k hsk`
  (equivalent elaboration), so every statement line stays byte-identical.
* `diff Statements_FINAL.lean Partial_Assembled.lean`: hunks `16a17 215c216,671 236a693,1057 256c1077,1103
  454a1302,4231 467a4245,5391 488a5413,5548 494c5554 615a5676,7109 626a7121,7233 634c7241,7260`; the ONLY removed
  lines are four `  sorry`.

## 3. Compile and remaining `sorry` (task 3)

**0 errors.**  `grep -c sorry` = 12 (10 bodies + 2 prose mentions).  The ten `sorry` declarations, exactly:

| assembled line | declaration | PLAN unit | status |
|---|---|---|---|
| 691 | `sg_daughters_products` | U103-D | leaf, open (unit not returned in wave 1) |
| 4243 | `s7_sliding_law_at` | U110-E | leaf, open |
| 5409 | `s7_bigon_law_at` | U110-K | leaf, open (bigon route waits on the R-II deletion constructor, U_S7G_REPORT §0) |
| 5565 | `s7_corner_product` (2nd conjunct; 1st proved in the frozen file) | U110-J | leaf, open |
| 7119 | `sft_same_sign` | U112-A (helpers `sfta_` adopted; leaf body not returned) | leaf, open |
| 7272 | `sft_loop` | U112-D | leaf, open |
| 7363 | `cb_singleton` | §6 row theorem | waits for row 100 (`cb_singleton_of_floor thm_floor`) |
| 7368 | `corner_values` | §6 row theorem | waits for row 100 |
| 7373 | `thm_C_S7` | §6 row theorem | waits for row 100 |
| 7378 | `thm_C_soft` | §6 row theorem | waits for row 100 |

Closed in this assembly (4 of the 10 leaves), `#print axioms` on a scratch copy of the assembled file:
`SM.sg_isolated_undominated`, `SM.sg_daughters_rotation`, `SM.s7_universal_extraction` = `[propext, Classical.choice,
Quot.sound]`; `SM.sft_mixed` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` (through `cornerStateSum`).
No `sorryAx` in any closed leaf.  The row assemblies `cb_singleton_of_floor`, `thm_C_S7_of_floor`,
`thm_C_soft_of_floor` still depend on `sorryAx` (through the six open leaves), as expected.

## 4. Statement byte-identity (task 4) — `tools/stmt_check.py`

For each of the 49 top-level declarations of `Statements_FINAL.lean` (4 `def`, 5 `structure`, 39 `theorem`, 1
`example`) the statement text — preceding docstring, `omit … in` modifier, declaration line(s) through the signature's
`:=` (trailing ` by` excluded; a `structure`'s whole field block) — must occur byte-for-byte EXACTLY ONCE in the
assembled file, in the frozen order, and its name must be declared exactly once.  Result: **49/49 PASS**
(`python3 tools/stmt_check.py` → exit 0).  Negative tests: a swapped binder (`hne : Λ₂ ≠ Λ₁`), a helper inserted
between a docstring and its declaration, and a re-declared frozen name each make the check FAIL.

## 5. Warnings (all pre-existing in the unit files; none in frozen text)

14 non-sorry warnings, all in the U_SFTA block (assembled lines 5802-6714): 8 × `if_neg` deprecated (→
`ite_eq_right`), 4 × "automatically included section variable(s) unused" (`sfta_insert_next_att`,
`sfta_markKey_visit_eq`, `sfta_soft_new_key`, `sfta_soft_zero_keys`), 2 × unreferenced variable names `S`, `T`.
Cosmetic; to be cleaned when U112-A's leaf is returned.  Every other unit block compiles with 0 non-sorry warnings,
as its report claims.

## 6. Notes for the executor

* Everything not listed in §3 is PROVED: the four row-level assemblies, `corner_values_i`, the bridge, the
  companions, and 488 unit helpers (11 blocks, 6626 lines).  The file is a draft under `work/drafts/`; nothing was
  written under `work/lean`.
* When U_S7A, U103-D (`sg_daughters_products`), U110-E/J/K and U112-A/D leaf bodies arrive, re-run
  `python3 tools/partial_assemble.py --units U_SGA,…,U_<new>` (the script accepts any unit list, rejects violations
  unit by unit, and is idempotent on the frozen file), then `stmt_check.py` and the compile.  U110-K's proof must
  come AFTER U110-G's and U110-H's blocks (U_S7H_REPORT §4): the current layout (H, I before `s7_bigon_law_at`; G
  after it) means K should either be placed below the two algebra leaves or G's block moved above `s7_bigon_law_at`
  — the assembler will need a `--move` of G's anchor at that point (frozen statements are not affected either way).
* Reproduce: `cd work/drafts/corner && python3 tools/partial_assemble.py && python3 tools/stmt_check.py &&
  cd ../../lean && lake env lean ../drafts/corner/Partial_Assembled.lean`.
