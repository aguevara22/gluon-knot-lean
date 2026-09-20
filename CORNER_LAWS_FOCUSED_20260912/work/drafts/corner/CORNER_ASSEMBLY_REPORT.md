# CORNER_ASSEMBLY_REPORT — corner chain, merge assembly of waves 1 + 2a + 2b (2026-09-15 21:00 UTC / 5:00pm ET)

Merge assembler subagent.  Inputs: `Wave1_Assembled.lean` (8,719 lines, sha256 `a2064c2f…6b569a`, the base), the wave-2a
product `Wave2a_Assembled.lean` (12,233 lines, `3bd5a98c…9b6802`) with `WAVE2A_ASSEMBLY_REPORT.md` and its three unit
files `W2_SGD.lean` (`0fc6100a…1b8b2d`), `W2_SFTC.lean` (`41540943…855ea`), `W2_SFTD.lean` (`7e412a93…086f6`) (written
against `Partial_Assembled.lean`, `85312954…081891`), and the two wave-2b unit files `W2_S7A2.lean` (`9b6803e8…09362b`,
written against `Wave1_Assembled.lean`) and `W2_S7E.lean` (`72dde145…e159c8`, written against `W2_S7A2.lean`) with their
reports.  Nothing was written under `work/lean`; `lake build` was not run.

Output: **`work/drafts/corner/Corner_Assembled.lean`** — **15,168 lines**, sha256
`d490b477d4da70e5c0407756679572bb46c0edbb6257d73798e44e3e415adc60`, produced by `python3 tools/corner_assemble.py`
(summary JSON kept as `tools/corner_assemble_summary.json`).

**Mandated check:** `cd work/lean && lake env lean ../drafts/corner/Corner_Assembled.lean` — **0 errors**, exit 0, 28 s warm
(load ≈ 10 on 8 cores).  27 warnings = **6 `declaration uses sorry`** (`s7_sliding_law_at` 8659, `s7_bigon_law_at` 9824, the
four §6 rows 15140/15145/15150/15155) + 21 cosmetic (§9, all pre-existing in the `sfta_`/`sftd_` blocks, none in frozen text,
none in the new 2b blocks).  **`grep -c sorry Corner_Assembled.lean` = 8** = 6 sorry bodies (8667, 9833, 15141, 15146, 15151,
15156) + the 2 prose mentions inherited from the frozen file (header line 25, §6 header line 15135).  No `#print`, `#eval`,
`#check`, `set_option`, `axiom` anywhere in the file.

**Context that changed while the waves ran (matters for §6-§8):** the executor has ALREADY ported the wave-2a state to the
library — `work/lean/SM/CornerChainStatements.lean`, `SM/CornerChainUnits.lean`, `SM/CBSingleton.lean`, `SM/CornerValues.lean`,
`SM/CSoft.lean` (all 20:00Z, byte-identical to `port/SM/*` except the header time line; `.olean`s built), and
`lean-declarations.json` marks **cb:singleton → `SM.cb_singleton` (SM.CBSingleton), lem:corner-values → `SM.corner_values`
(SM.CornerValues), thm:C-soft → `SM.thm_C_soft` (SM.CSoft) as `accepted`**; thm:C-S7 → `SM.thm_C_S7` is `pending`
(module empty).  `SM/Comparison.lean` and `SM/CInherits.lean` (20:26Z) wait for `SM.thm_C_S7` (`thm_comparison_of hR thm_C_S7
thm_C_soft`, `cor_C_inherits_of …`).  So the only material of this file NOT yet in the library is the wave-2b material
(`s7a2_`, `s7e_`) and the open row-110 declarations.

## 1. Diff audit — every unit file against ITS OWN base (task 1)

Method (`tools/corner_assemble.py`, the wave-2a classifier generalised to per-unit bases and prefix SETS): GNU `diff` in
normal format; a hunk is CLEAN iff it is a pure insertion (helper block — audited: every top-level declaration carries one of
the unit's prefixes or lives in a namespace carrying it; no `sorry`/`#print`/`#eval`/`#check`/`axiom`/`import`/`set_option`
inside; no name declared twice) or a `c`-hunk whose removed lines are exactly `  sorry` inside the body of THAT unit's own
PLAN_FINAL §4 leaf (located by scanning back in the base to the enclosing declaration).  A `d`-hunk, a changed base line, another
unit's leaf, or a §6 row theorem touched = VIOLATION → unit rejected.

| unit | base | hunks vs base | removed lines | block (decls) | body | verdict |
|---|---|---|---|---|---|---|
| `W2_SGD` (U103-D, `sgd_`) | `Partial_Assembled.lean` | `672a673,838`, `691c857,868` | `  sorry` (691, `sg_daughters_products`) | 166 lines, 7 | 12 lines | **clean** |
| `W2_SFTC` (U112-C, `sftc_`) | `Partial_Assembled.lean` | `7109a7110,7802`, `7119c7812,7865` | `  sorry` (7119, `sft_same_sign`) | 693 lines, 36 | 54 lines | **clean** |
| `W2_SFTD` (U112-D, `sftd_`) | `Partial_Assembled.lean` | `7261a7262,9827`, `7272c9838,9863` | `  sorry` (7272, `sft_loop`) | 2566 lines, 188 | 26 lines | **clean** |
| `Wave2a_Assembled` (the 2a product, source of the 2a hunks) | `Wave1_Assembled.lean` | `672a673,838`, `691c857,868`, `8438a8616,9308`, `8448c9318,9371`, `8590a9514,12079`, `8601c12090,12115` | three `  sorry` (691, 8448, 8601) | the three blocks above | the three bodies above | **clean, adopted** |
| `W2_S7A2` (U110-A2 helper unit, `s7a2_`) | `Wave1_Assembled.lean` | `5543a5544,6257` | none | 714 lines (incl. 2 trailing blanks), 60 decls by the scanner (the report counts 50: it does not count the `s7a2_…_of_ne`/simp-lemma one-liners separately) | — | **clean, adopted** |
| `W2_S7E` (U110-E leaf unit, `s7e_`) | `W2_S7A2.lean` | `6256a6257,8477` | none | 2221 lines, 179 decls (report: 175) | **none — the leaf `s7_sliding_law_at` keeps its `sorry`** (as the report says) | **clean, adopted** |

**Violations: none.**  No unit changed a statement, definition, structure, name, docstring or import of the frozen file; no unit
touched a §6 row theorem or another unit's leaf; no added text contains a forbidden token; no import was added by any unit (the
header stays the 17 frozen imports).  Consistency checks (all in the JSON summary): (i) the 2a blocks and bodies extracted from
`Wave2a_Assembled.lean` vs `Wave1_Assembled.lean` are TEXT-IDENTICAL to those of the three unit files vs
`Partial_Assembled.lean` (`2a_blocks_equal_units_blocks = true`, `2a_bodies_equal_units_bodies = true`), and re-running
`tools/wave2a_assemble.py` from `Partial_Assembled.lean` reproduces `Wave2a_Assembled.lean` byte for byte (sha match) — so the
rebase rule of WAVE1 §10 was applied correctly by the 2a assembler and needed no re-application here; (ii) `W2_S7E.lean` vs
`Wave1_Assembled.lean` is ONE insertion `5543a5544,8478` whose first 713 lines are `W2_S7A2`'s block — E was built on A2, so E's
hunk is taken against `W2_S7A2.lean` (2221 E-only lines) and the A2 block is adopted once (no duplicated declaration; §2).

## 2. Assembly (task 2)

Sequential patch application on a line-id model (anchors resolve by identity of the base line, never by line arithmetic): the
A2 block is inserted after Wave1 line 5543; the output is then verified **byte-identical to `W2_S7A2.lean`** (checkpoint
`output == W2_S7A2.lean = true`), so E's anchor (A2 line 6256) is resolved on it and E's block inserted; then the six 2a hunks
(anchored at Wave1 lines 672/691/8438/8448/8590/8601, all outside the 2b insertion region).  Import union: nothing to add.
De-duplication / rename-on-clash: **not exercised** (`dedup_dropped = []`, `renamed = []`; no declaration name occurs twice in
the output, 1,096 declarations by the comment-aware scanner).  Every block occurs exactly once, as one contiguous slice:

| block | assembled lines | inside | anchor |
|---|---|---|---|
| `sgd_` (W2_SGD, 7 decls) | 673-837 (+ blank 838) | `section Singleton` | after the `sgc_` block, before the docstring of `sg_daughters_products` (842) |
| `s7a2_` (W2_S7A2, 60 decls) | **5721-6432** (+ blanks 6433) | `section VertexEdge` (sub-sections `S7A2Marks` 5746, `S7A2Germ` 5953, `S7A2Family` 6110, `S7A2Assembly` 6335) | after U110-D's `s7d_cornerCoefficient_transport` (5720) |
| `s7e_` (W2_S7E, 179 decls) | **6434-8653** (+ blanks 8654-8655) | `section VertexEdge` (sub-sections `S7EAlgebra` 6437 … `S7EContactRepack` 8608) | directly after the `s7a2_` block, before the docstring of `s7_sliding_law_at` (8656) |
| `sftc_` (W2_SFTC, 36 decls) | 11551-12241 (+ blanks) | `section Soft` | after the `sfta_` block, before the docstring of `sft_same_sign` (12246) |
| `sftd_` (W2_SFTD, 188 decls) | 12449-15013 (+ blank) | `section Soft` | after `sft_mixed`, before the docstring of `sft_loop` (15018) |

Leaf bodies replaced in place: `sg_daughters_products` 857-868, `sft_same_sign` 12253-12306, `sft_loop` 15025-15050 (each
verified in place, occurring once).  The A2 hunk carries two trailing blank lines and E's block sits between them (that is how
`W2_S7E.lean` itself is laid out) — the A2 declarations are contiguous; the contiguity check strips trailing blanks of a hunk.

**Diffs against the predecessors (removed lines are ONLY `  sorry`):**
* `diff Wave1_Assembled.lean Corner_Assembled.lean` = `672a673,838 691c857,868 5543a5721,8655 8438a11551,12243 8448c12253,12306
  8590a12449,15014 8601c15025,15050` (removed: three `  sorry`).
* `diff Wave2a_Assembled.lean Corner_Assembled.lean` = **`5720a5721,8655`** only — the file is exactly the wave-2a product plus the
  2,935-line 2b insertion (so everything the executor ported from `Wave2a_Assembled.lean` is unchanged here, line for line up to 5720
  and shifted by +2935 after).
* `diff W2_S7E.lean Corner_Assembled.lean` = `672a673,838 691c857,868 11373a11551,12243 11383c12253,12306 11525a12449,15014
  11536c15025,15050` (removed: three `  sorry`) — the 2a hunks and nothing else.
* `diff Statements_FINAL.lean Corner_Assembled.lean` removes exactly **eight `  sorry`** (the 8 closed leaves).

**Rebase rules.**  Wave2a line `L` → Corner: `L` if `L ≤ 5720`, else `L + 2935`.  Wave1 line `L` → Corner: `L` if `L ≤ 672`;
`+166` if `≤ 691`; `+177` if `≤ 5543`; `+3112` if `≤ 8438`; `+3805` if `≤ 8448`; `+3858` if `≤ 8590`; `+6424` if `≤ 8601`; `+6449`
beyond (8719 + 6449 = 15168).  W2_S7E line `L` → Corner: `L` if `L ≤ 672`; `+166` if `≤ 691`; `+177` if `≤ 11373`; `+870` if
`≤ 11383`; `+923` if `≤ 11525`; `+3489` if `≤ 11536`; `+3514` beyond (11654 + 3514 = 15168).  Any wave-3 unit should be written
against `Corner_Assembled.lean` and classified with `tools/corner_assemble.py`'s machinery (add a `UNITS` row with its base).

## 3. Remaining `sorry` — the unproved leaves, exactly (task 3)

| assembled line [sorry] | declaration | PLAN unit | status |
|---|---|---|---|
| 8659 [8667] | `s7_sliding_law_at` | U110-E (wave 2b) | **OPEN.**  W2_S7E proved PLAN §3.3 sliding (1) the spectator sector (`s7e_exists_spectatorSector`) and (4) the algebra (`s7e_law_of_sectors`), and REDUCED the leaf to `s7e_sliding_law_at_of_contact : (∃ δ > 0, ∀ t < δ, s7e_ContactSector hn h h₁ h₂ t) → <leaf statement>` with `s7e_contactSector_of_pivotSplit` producing the sector from two `s7b_PivotSplit` instances + the termwise identity `hterm`.  What remains = sliding (2)-(3): the interlacement transfer `s7b_PivotSplit … x` on BOTH sides (U_S7B_REPORT §2.2, est. 500-800 lines), `s7b_SlidingTransport.ret` on both sides (U_S7B §2.1, est. 600-900), the per-carrier coefficient transport to the halves with `hr` = rotation equality THROUGH the contact by principal-angle addition (eq. s7c:turn-short-a/b; NOT in the library, explicitly out of A2's scope), the ordered corner bijection for `s7c_carrierWeight_refine` (est. 400-600), then `s7c_sliding_selector_difference`.  W2_S7E_REPORT estimates 2,500-4,000 lines.  Nothing believed false; no missing hypothesis in the frozen statement. |
| 9824 [9833] | `s7_bigon_law_at` | U110-K (wave 3) | OPEN; WAVE1 §7 declared it BLOCKED on a generic R-II deletion witness.  **New since then:** `work/lean/SM/BigonDeletion.lean` (ported 20:20Z from the moves lane, 5,374 lines) provides `m7_riiData : RIIData C.U (B.reducedDiagram C) D` (line 4959, "the R-II site … the reduced diagram is the crossing-free side") with `BigonData`, `reducedDiagram`, `m3_sign`, `m4_clean'`, `um5_outerEquiv` — U110-K should be re-planned against it before accepting the "bigon stated, not proved" sentence. |
| 15140 [15141] | `cb_singleton` | §6 row 103 | `sorry` by design in the draft; **closed in the library** as `SM.cb_singleton := cb_singleton_of_floor thm_floor` (SM/CBSingleton.lean, accepted); the composition re-tested here sorry-free (§7) |
| 15145 [15146] | `corner_values` | §6 row 105 | idem, `SM.corner_values := corner_values_of_floor thm_floor` (SM/CornerValues.lean, accepted); re-tested sorry-free (§7) |
| 15150 [15151] | `thm_C_S7` | §6 row 110 | `thm_C_S7_of_floor thm_floor` typechecks but inherits `sorryAx` from the two open leaves — NOT portable |
| 15155 [15156] | `thm_C_soft` | §6 row 112 | idem, `SM.thm_C_soft := thm_C_soft_of_floor thm_floor` (SM/CSoft.lean, accepted); re-tested sorry-free (§7) |

Unit leaves: **8 of 10 PROVED** (`sg_isolated_undominated`, `sg_daughters_products`, `sg_daughters_rotation`,
`s7_universal_extraction`, `s7_corner_product`, `sft_same_sign`, `sft_mixed`, `sft_loop`).  **Own proving (≤ 45 min budget): not
attempted** — neither open leaf is a small gap (U110-E's remainder is a 2,500-4,000-line unit needing a geometric input the library
lacks; U110-K is a wave-3 unit), and the §6 rows are compositions, not gaps (three already accepted in the library, tested in §7).

## 4. Compile and axioms (task 4)

**Exhaustive `#print axioms`** on a scratch copy (scratchpad `Corner_axioms.lean` = the assembled file + one `#print axioms` per
declaration between `end` and `end SM`; **1,096 queries, 1,096 answers parsed** (prime- and line-wrap-tolerant), 0 errors, 32 s).
Axiom union over the whole file: `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — all in
`work/lean/axiom-policy.json` (standard + literature) — plus `sorryAx` in EXACTLY these 8 declarations: `s7_sliding_law_at`,
`s7_bigon_law_at`, `thm_C_S7_of`, `thm_C_S7_of_floor`, `cb_singleton`, `corner_values`, `thm_C_S7`, `thm_C_soft` (the last four only
because their draft bodies are `sorry`).  **No helper of any unit depends on `sorryAx`.**

| declaration (all `SM.`) | axioms |
|---|---|
| `cb_singleton_of_floor` (row 103 ← thm:floor) | `[propext, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness]` — sorry-free |
| `corner_values_i`, `corner_values_of_singleton`, `corner_values_of_floor` (row 105) | same six — sorry-free |
| `thm_C_soft_of_cornerValues`, `thm_C_soft_of_floor` (row 112 ← 105 ← 100) | same six — sorry-free |
| `thm_C_S7_of` | `[propext, Classical.choice, Quot.sound, lit_homfly] + sorryAx` |
| `thm_C_S7_of_floor` | the six `+ sorryAx` |
| `s7_sliding_law_at` (open leaf) | `[propext, Classical.choice, Quot.sound, lit_homfly] + sorryAx` |
| `CS7Data.sliding`, `CS7Data.bigon` (companions) | `[propext, Classical.choice, Quot.sound, lit_homfly]` — sorry-free |
| leaves `sg_daughters_products`, `sft_same_sign`, `sft_loop` | the six, no `sorryAx` |
| leaves `sg_isolated_undominated`, `sg_daughters_rotation`, `s7_universal_extraction`, `s7_corner_product` | `[propext, Classical.choice, Quot.sound]` |
| leaf `sft_mixed` | `+ lit_homfly` |
| bridge `carrierUniformOrOneDissent_of_signed` | `[propext, Classical.choice, Quot.sound]`; `FloorTheoremData.slot_le_of_signed` `+ lit_homfly` |
| **new 2b helpers `s7a2_` (60)** | all 60: `[propext, Classical.choice, Quot.sound]` (incl. `s7a2_carrierRotation_eq`, `s7a2_cornerFamily_regular`, `s7a2_cornerFamily_continuousOn`) |
| **new 2b helpers `s7e_` (179)** | 160 standard, 5 `[propext, Quot.sound]`; 9 `+ lit_homfly` (`s7e_term`, `s7e_term_of_not`, `s7e_term_of_decomposition`, `s7e_cornerStateSum_eq_sum_term`, `s7e_ContactSector`, `s7e_SpectatorSector`, `s7e_law_at_of_sectors`, `s7e_sliding_law_at_of_sectors`, `s7e_contactSector_of_pivotSplit` — through `C_X1.selector_form`); 5 the six (`s7e_coef_eq`, `s7e_term_eq`, `s7e_spectatorSector_of`, `s7e_exists_spectatorSector`, `s7e_sliding_law_at_of_contact` — through U110-D's record route, as `s7d_cornerCoefficient_eq_of_cut`) |
| 2a helpers (`sgd_` 7, `sftc_` 36, `sftd_` 188) | as WAVE2A §4 (unchanged): `sgd_` 3 std + 4 `+lp_lm`; `sftc_` 35 std-or-less + 1 six; `sftd_` 180 std-or-less + 6 six + 2 `+lit_homfly` |

Per-declaration table: scratchpad `corner_axioms.json`.  Everything W2_S7A2_REPORT and W2_S7E_REPORT claim about their axioms is
confirmed.

## 5. Statement byte-identity (task 5)

`python3 tools/stmt_check.py Corner_Assembled.lean`: for each of the 49 top-level declarations of `Statements_FINAL.lean` (4 `def`,
5 `structure`, 39 `theorem`, 1 `example`) the statement text (preceding docstring, `omit … in`, declaration line(s) through the
signature's `:=`; a `structure`'s whole field block) occurs byte-for-byte EXACTLY ONCE, in the frozen order, and the name is declared
exactly once: **49/49 PASS** (exit 0).  Independently, the diffs of §2 remove only `  sorry` lines.  The §0 copy span (lines 60-92)
is still byte-identical (`cmp`) to `work/lean/SM/CarrierFloor.lean:377-408`.

## 6. Name-clash scan (task 6) — read against the CHANGED library

`tools/clash_scan.py` (prefix regex widened to `s7[a-z]2?_` for `s7a2_`; scratch copy) over the **692** `.lean` files / **21,023**
declarations now in `work/lean` (`.lake` excluded): **1,048 new declarations** in the assembled file (809 of waves 1/2a + 60 `s7a2_`
+ 179 `s7e_`), **0 duplicated names inside the file**.  Full-name hits: **809 — every one of them in `SM/CornerChainUnits.lean`**,
i.e. the executor's 20:00Z port of these very declarations, and each is **byte-identical** (statement + body paragraph) to the
library copy (`809 identical, 0 differing`).  These are not clashes but the same declarations already landed; the assembled file
must therefore NOT be ported wholesale next to `SM/CornerChainUnits.lean` (it would redeclare all 809) — see §8.  **Genuine
clashes of the NEW material: 0** — no `s7a2_`/`s7e_` name (full or short) exists anywhere in `work/lean`; 0 short-name
coincidences for them either (the 809 short-name coincidences reported are the same library copies).  Prefix statistics: `sgb_` 31,
`sgc_` 6, `sgd_` 7, `sge_` 22, `s7a_` 91, `s7a2_` 60, `s7b_` 151, `s7c_` 49, `s7d_` 27, `s7e_` 179, `s7g_` 13, `s7h_` 19, `s7i_` 49,
`sfta_` 114, `sftb_` 6, `sftc_` 36, `sftd_` 188; unprefixed short names live only inside prefixed namespaces.  Known redundancies
with accepted lemmas (WAVE2A §6, unchanged; different names, no clash) stand.

## 7. Row closures (task 7)

Scratch copy **`Corner_RowClosureProbe.lean`** (filed next to the drafts as evidence; 15,158 lines, sha256 `8f180f07…bad188`): the
assembled file with (i) the §0 copies `AllLeftOrOneRight` / `CarrierUniformOrOneDissent` / `FloorTheoremData` (lines 60-92)
DELETED (2-line note left), (ii) `import SM.CarrierFloorRows` appended to the 17-line import header, (iii) the four §6 bodies
composed exactly as §6's docstrings prescribe — `exact cb_singleton_of_floor SM.thm_floor`, `exact corner_values_of_floor
SM.thm_floor`, `exact thm_C_S7_of_floor SM.thm_floor`, `exact thm_C_soft_of_floor SM.thm_floor` — and (iv) `#print axioms` +
`example : CbSingletonData ∧ CornerValuesData ∧ CSoftData := ⟨cb_singleton, corner_values, thm_C_soft⟩` before `end SM`.
`cd work/lean && lake env lean ../drafts/corner/Corner_RowClosureProbe.lean`: **0 errors**, 28 s; `declaration uses sorry` only for
`s7_sliding_law_at`, `s7_bigon_law_at` and `thm_C_S7`.  (A first run failed for a reason worth recording: `Corner_Assembled.lean`
starts DIRECTLY with `import SM.CBProducts` on line 1 — no header comment as in the earlier probes — so a header comment must be
inserted after the import run, never prepended to line 1.)

| row theorem (composition) | axioms |
|---|---|
| `SM.cb_singleton := cb_singleton_of_floor SM.thm_floor` (row 103) | `[propext, Classical.choice, Quot.sound, lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact]` — **registered only, no `sorryAx`** (= the axioms of `SM.thm_floor`) |
| `SM.corner_values := corner_values_of_floor SM.thm_floor` (row 105) | same nine — **no `sorryAx`** |
| `SM.thm_C_soft := thm_C_soft_of_floor SM.thm_floor` (row 112, fixed name) | same nine — **no `sorryAx`** |
| `SM.thm_C_S7 := thm_C_S7_of_floor SM.thm_floor` (row 110, fixed name) | same nine **`+ sorryAx`** — still needs BOTH open leaves `s7_sliding_law_at` (U110-E) and `s7_bigon_law_at` (U110-K); the companions `CS7Data.sliding`/`.bigon` are sorry-free |

These three closures are exactly what the executor accepted at 20:00Z (`SM/CBSingleton.lean:12`, `SM/CornerValues.lean:12`,
`SM/CSoft.lean:14`); the probe confirms they remain valid on the merged file with the 2b blocks present under the enlarged import
closure (no ambiguity introduced by `SM.CarrierFloorRows`' closure anywhere in the 15k lines).

## 8. Port plan (task 8) — what is left to port, and where

**Already in the library (do not re-port):** everything of `Corner_Assembled.lean` outside the 2b insertion — `SM/CornerChainStatements.lean`
(17 frozen declarations, `import SM.CarrierFloor`, §0 copies deleted), `SM/CornerChainUnits.lean` (829 declarations = the 809 helpers
+ the closed leaves + the conditional assemblies of rows 103/105/112), `SM/CBSingleton.lean`, `SM/CornerValues.lean`, `SM/CSoft.lean`
(rows 103/105/112, accepted).  PORT_REPORT.md documents that port from `Wave2a_Assembled.lean`; since `Corner_Assembled = Wave2a +
5720a5721,8655`, every source line it cites is unchanged here up to 5720 and shifted by +2935 after.

**(a) NEW module for the sliding companion of row 110 — proposed `SM/CS7Sliding.lean`** (library material, sorry-free): the two 2b
blocks VERBATIM, i.e. assembled lines **5721-8653** (`s7a2_` 5721-6432, `s7e_` 6434-8653), wrapped as `import SM.CornerChainUnits` +
the frozen preamble (lines 45-51: `namespace SM` / `open Link Carrier` / `attribute [local instance] Classical.propDecidable` /
`noncomputable section`) + `section VertexEdge` / `variable {n : ℕ} [NeZero n]` (the §4 opener, lines 1420-1422) + `end VertexEdge` /
`end` / `end SM`.  **Tested:** `Corner_CS7SlidingProbe.lean` (filed next to the drafts; 2,956 lines, sha256 `23c5a5ec…4e7f95`, exactly this
module with a probe header) compiles against the BUILT library — `cd work/lean && lake env lean ../drafts/corner/Corner_CS7SlidingProbe.lean`:
**0 errors, 0 warnings, 17 s**.  So the 2b material depends only on `SM.CornerChainUnits` (it uses `s7a_`, `s7b_`, `s7c_`, `s7d_` and the
accepted `vertex_sides`/`VertexLocalData`/`C_X1.selector_form` …; nothing from `s7h_`/`s7i_`/`s7g_`, which sit below it in the draft).
Header line 1 per the executor's template ("Ported HH:MMZ 2026-09-15 from work/drafts/corner/Corner_Assembled.lean lines 5721-8653 …").
The only text to reword inside the blocks: the E header docstring's "Probe section." (6435-6436) — cosmetic.  Expected axioms: §4's
2b rows (standard, `+ lit_homfly`, the six) — all registered.  `lean-declarations.json`: nothing to map (helper material); thm:C-S7 stays
pending.

**(b) Row 110 — stays in the draft until wave 2b/3 close the leaves:** assembled lines **8656-8668** (`s7_sliding_law_at` + docstring,
`sorry` 8667), **9816-9834** (`s7_bigon_law_at`, `sorry` 9833), **10008-10039** (`thm_C_S7_of`, `thm_C_S7_of_floor`; `sorryAx`),
**15148-15151** (`thm_C_S7`, fixed name).  When both leaves are proved: module `SM/CS7.lean` importing `SM.CS7Sliding` (+ the wave-3
bigon helper module) and `SM.CarrierFloorRows`, receiving those spans verbatim and `theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor
thm_floor` (statement line 15150 up to ` by`); then `SM.thm_comparison := thm_comparison_of hR thm_C_S7 thm_C_soft` (SM/Comparison.lean
header) and `SM.cor_C_inherits := cor_C_inherits_of hR thm_C_S7 thm_C_soft` (SM/CInherits.lean header) can be declared.  A wave-3 unit
for U110-K should be written against `Corner_Assembled.lean` (K's proof must be placed BELOW the `s7g_` block, WAVE1 §3/U_S7H §4, or
G's anchor moved above `s7_bigon_law_at`).

**(c) If the executor prefers to REGENERATE the two big modules from `Corner_Assembled.lean`** (instead of (a)), the PORT_REPORT §1
line ranges become: Statements = 1-17 (+ `import SM.CarrierFloor`), 18, 44-52, 55-59, 93-202, 1315-1342, 1397-1406, 1416-1474,
**10040-10094**, **15133-15134**, **15166-15168**; Units = 44-52, 182-187, 203-1322, 1343-1396, 1407-1423, **1475-8653** (now including
the 2b blocks), **8669-9815**, **9835-10007**, **10040-10049**, **10095-15134**, **15166-15168**; excluded = 19-43 (header, reword;
`sorry` at 25), 53-54 (§0 heading, reword), 60-92 (the three §0 copies, DELETE), 8656-8668, 9816-9834, 10008-10039 (row 110),
15135-15165 (§6 with `sorry` at 15135/15141/15146/15151/15156 and the §7 `example` 15163-15164 whose first conjunct is
`thm_C_S7_of_floor hF` — reduced in SM/CSoft.lean to `⟨cb_singleton, corner_values, thm_C_soft⟩`).  Every boundary line was verified
(`10040 = end VertexEdge`, `10050 = /-- **thm:C-soft as printed**`, `10095 = /-! ### Leaves of row 112`, `15133 = end Soft`,
`15166 = end`).  This route re-declares the 809 ported names — only acceptable as a REPLACEMENT of `SM/CornerChainUnits.lean`, never
alongside it (§6).

**Lines with `sorry` / `#print` / `#eval` to reword or exclude:** `sorry` prose at 25 (header) and 15135 (§6 heading); `sorry` bodies at
8667, 9833 (open leaves — excluded from any port), 15141/15146/15156 (already the one-liners in the library row modules), 15151
(excluded with row 110).  No `#print`, `#eval`, `#check`, `set_option` exists in `Corner_Assembled.lean`; the two filed probes carry
`#print axioms` and are NOT port products.  Docstring cross-references to "W2_*_REPORT.md", "PLAN_FINAL", "wave", "Probe section" are
cosmetic.

## 9. Warnings (cosmetic; none in frozen text, none in the 2b blocks)

21 non-sorry warnings, all pre-existing in the `sfta_`/`sftd_` blocks (WAVE2A §7 list, shifted by +2935): 8 × `if_neg` deprecated
(10981-11155), 6 × unused auto-included section variable (`sfta_insert_next_att` 10243, `sfta_markKey_visit_eq` 11024,
`sfta_soft_new_key` 11106, `sfta_soft_zero_keys` 11142, `sftd_soft_key_a` 13872, `sftd_soft_key_b` 13878), 2 × `push_neg` deprecated
(13912, 13953), 5 × unreferenced binder `S`/`T`/`hS` (10381, 13013, 14968).  They are in the library already (verbatim port); fixes
change helper text only.  The `s7a2_` and `s7e_` blocks compile with **0 warnings** (E silenced its linter hits with `omit [NeZero n] in`).

## 10. Leaves reported false

**None.**  W2_S7A2_REPORT and W2_S7E_REPORT both state "nothing believed false / no missing hypothesis" (E: the only implicit radius
the spectator sector needed beyond A2's interval data is `vertexEdge_contact_tests`', intersected into δ); nothing found here contradicts
them or the earlier reports.

## 11. Reproduce

```
cd work/drafts/corner
python3 tools/corner_assemble.py --out Corner_Assembled.lean      # exit 0; JSON summary = tools/corner_assemble_summary.json
python3 tools/stmt_check.py Corner_Assembled.lean                 # 49/49 PASS
cd ../../lean
lake env lean ../drafts/corner/Corner_Assembled.lean              # 0 errors, 6 sorry warnings + 21 cosmetic
lake env lean ../drafts/corner/Corner_RowClosureProbe.lean        # 0 errors; rows 103/105/112 sorry-free, 110 sorryAx
lake env lean ../drafts/corner/Corner_CS7SlidingProbe.lean        # 0 errors, 0 warnings (2b blocks on SM.CornerChainUnits)
```
Files written: `Corner_Assembled.lean`, `Corner_RowClosureProbe.lean`, `Corner_CS7SlidingProbe.lean`, `tools/corner_assemble.py`,
`tools/corner_assemble_summary.json`, this report.  Scratch (scratchpad, not products): `Corner_axioms.lean`, `corner_axioms.json`,
`clash_scan_corner.json`, the compile logs.
