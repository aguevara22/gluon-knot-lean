# WAVE1_ASSEMBLY_REPORT — corner chain, wave-1 assembly (2026-09-15 18:40 UTC / 2:40pm ET)

Assembler subagent.  Inputs: the frozen `work/drafts/corner/Statements_FINAL.lean` (764 lines, sha256
`c2e98430…ea52f`) and the thirteen wave-1 unit files `U_{S7G,S7B,S7A,SGE,SGA,SGB,SGC,SFTA,SFTB,S7C,S7D,S7H,S7I}.lean`
with their reports (`U_SFTA_REPORT.md` is still missing; the unit file was verified directly, §1).  This supersedes
`PARTIAL_ASSEMBLY_REPORT.md` (18:10 UTC, twelve units, `U_S7A` excluded): `U_S7A` has now landed and is adopted.

Output: **`work/drafts/corner/Wave1_Assembled.lean`** (8719 lines, sha256 `a2064c2f…6b569a`), produced by
`python3 tools/partial_assemble.py --out Wave1_Assembled.lean --units U_SGA,U_SGB,U_SGC,U_SGE,U_SFTA,U_SFTB,U_S7A,U_S7B,U_S7C,U_S7D,U_S7G,U_S7H,U_S7I,U_S7J0`
(the 14th "unit", `U_S7J0.lean`, is the assembler's own closure of one small gap, §3); statement identity checked by
`python3 tools/stmt_check.py Wave1_Assembled.lean`.

**Mandated check:** `cd work/lean && lake env lean ../drafts/corner/Wave1_Assembled.lean` — **0 errors**, exit 0, 22 s
warm (load ≈ 10.5 on 8 cores).  23 warnings = **9 `declaration uses sorry`** (exactly the 5 open leaves + the 4 §6 row
theorems, §3) + 14 cosmetic linter/deprecation warnings, all pre-existing inside the U_SFTA block (§5).
`grep -c sorry Wave1_Assembled.lean` = **11** = 9 sorry bodies + the 2 prose mentions inherited from the frozen file
(header line 25, §6 header line 8686).

## 1. Diff audit of the thirteen units against Statements_FINAL.lean (task 1)

Method (`tools/partial_assemble.py`, unchanged from the partial assembly): GNU `diff` in normal format, every hunk
classified.  CLEAN = a pure insertion (`Na…`: a helper block, or an `import` line inside the import header) or a `c`-hunk
whose REMOVED lines are exactly the `sorry` body of one of the ten PLAN_FINAL §4 leaves (`  sorry` alone, or `<statement
tail> := by` + `  sorry` replaced by `<statement tail> :=` + a term).  Anything else — a deleted or changed frozen line, or a
§6 row theorem's `sorry` touched — is a VIOLATION and the unit is not adopted.

| unit | PLAN row | hunks vs frozen | removed frozen lines | classification | verdict |
|---|---|---|---|---|---|
| U_SGA | U103-A leaf `sg_isolated_undominated` | `215c215,257` | `  sorry` (215) | leaf body, 43 lines | **clean, adopted** |
| U_SGB | U103-B helpers `sgb_` | `216a217,559` | none | helper block, 343 lines | **clean, adopted** |
| U_SGC | U103-C helpers `sgc_` | `216a217,286` | none | helper block, 70 lines | **clean, adopted** |
| U_SGE | U103-E leaf `sg_daughters_rotation` + `sge_` | `236a237,601`, `256c621,647` | `  sorry` (256) | helper block 365 + leaf body 27 | **clean, adopted** |
| U_SFTA | U112-A helpers `sfta_` (no report) | `615a616,2049` | none | helper block, 1434 lines | **clean, adopted** (unit file compiles alone: 0 errors, 14 sorry warnings) |
| U_SFTB | U112-B leaf `sft_mixed` + `sftb_` | `626a627,739`, `634c747,766` | `  sorry` (634) | helper block 113 + leaf body 20 | **clean, adopted** |
| U_S7A | U110-A helpers `s7a_` | `16a17`, `453a455,1766` | none | `import SM.VertexSides` + helper block 1312 lines (88 decls) | **clean, adopted** (import unioned) |
| U_S7B | U110-B helpers `s7b_` | `16a17`, `453a455,2168` | none | `import SM.VertexSides` + helper block 1714 lines | **clean, adopted** (import unioned) |
| U_S7C | U110-C helpers `s7c_` | `454a455,1120` | none | helper block, 666 lines | **clean, adopted** |
| U_S7D | U110-D helpers `s7d_` | `454a455,1004` | none | helper block, 550 lines | **clean, adopted** |
| U_S7G | U110-G leaf `s7_universal_extraction` + `s7g_` | `488a489,624`, `493,494c629,630` | 493 `… := by` → `… :=`, 494 `  sorry` | helper block 136 + one-line term body | **clean, adopted** (normalised, §2) |
| U_S7H | U110-H helpers `s7h_` | `467a468,782` | none | helper block, 315 lines | **clean, adopted** |
| U_S7I | U110-I helpers `s7i_` | `467a468,1299` | none | helper block, 832 lines | **clean, adopted** |

**Violations: none.**  No unit changed a statement, definition, structure, name, docstring or import of the frozen file
(the only header change is the ADDED import of `U_S7A`/`U_S7B`); no unit touched a §6 row theorem or another unit's
leaf; no unit's added text contains `sorry`.  Cross-references between units occur only in docstrings; no unit's CODE
depends on another unit's helpers, so the blocks are order-independent.  Both `U_S7A` and `U_S7B` anchor at frozen line
453 — they are placed in unit order (A, then B) and both compile in that order.

## 2. Assembly (task 2)

`Wave1_Assembled.lean` = `Statements_FINAL.lean` with every clean hunk applied:

* the five leaf bodies replaced in place (`sg_isolated_undominated`, `sg_daughters_rotation`, `sft_mixed`,
  `s7_universal_extraction`, and `s7_corner_product`'s 2nd conjunct — the assembler's own, §3);
* the twelve helper blocks inserted verbatim and CONTIGUOUSLY at each unit's own anchor (blocks sharing an anchor
  follow in unit order; a blank separator line is added only where two non-blank lines would otherwise touch).
  Verified programmatically: each block occurs as ONE contiguous slice of the assembled file, exactly once —

  | block | assembled lines | inside |
  |---|---|---|
  | U_SGB | 260-602 | `section Singleton`, after `sg_isolated_undominated` |
  | U_SGC | 603-672 | idem, before the docstring of `sg_daughters_products` |
  | U_SGE | 693-1057 | `section Singleton`, before the docstring of `sg_daughters_rotation` |
  | U_S7A | 1301-2612 | `section VertexEdge`, before the docstring of `s7_sliding_law_at` |
  | U_S7B | 2613-4326 | idem (directly after U_S7A) |
  | U_S7C | 4328-4993 | idem |
  | U_S7D | 4994-5543 | idem |
  | U_S7H | 5557-5871 | `section VertexEdge`, before the docstring of `s7_bigon_law_at` |
  | U_S7I | 5872-6703 | idem |
  | U_S7G | 6725-6860 | `section VertexEdge`, before the docstring of `s7_universal_extraction` |
  | U_SFTA | 7005-8438 | `section Soft`, before the docstring of `sft_same_sign` |
  | U_SFTB | 8450-8562 | `section Soft`, before the docstring of `sft_mixed` |

  The units' own `section … end`, `namespace … end`, `variable`, `omit [NeZero n] in` wrappers are kept exactly as
  written (the frozen `namespace SM`, `open Link Carrier`, `attribute [local instance] Classical.propDecidable`,
  `noncomputable section` still enclose everything; `end`/`end SM` close at lines 8717/8719).
* **Import union**: `import SM.VertexSides` (asked for identically by U_S7A and U_S7B; lem:wall-sides (V) is unreachable
  from the 16 frozen imports) appended once after `import SM.GermSides` (line 17).  The frozen text and the other ten
  blocks compile unchanged under the enlarged import set.
* **One normalisation**: U_S7G's term-mode leaf body (`… :=` / `  s7g_extraction_of_skein FH FL FA k hsk`) is written
  as `… := by` / `  exact s7g_extraction_of_skein FH FL FA k hsk`, so frozen line 493 stays byte-identical.
* **De-duplication / rename-on-clash**: not exercised — no identical helper appears twice and no two units declare the
  same full name (`dedup_dropped = []`, `renamed = []`; the assembled file has no duplicated declaration name).
* `diff Statements_FINAL.lean Wave1_Assembled.lean` = `16a17 215c216,671 236a693,1057 256c1077,1103 454a1302,5543
  467a5557,6703 488a6725,6860 494c6866 505c6877,6894 615a7005,8438 626a8450,8562 634c8570,8589`; the ONLY removed lines
  are five `  sorry`.
* Relation to the partial assembly: `diff Partial_Assembled.lean Wave1_Assembled.lean` = `1301a1302,2613` (the U_S7A
  block) + `5565c6877,6894` (the `s7_corner_product` body; removed line `  sorry`).  **Rebase rule for anything built on
  `Partial_Assembled.lean`** (the wave-2 files `W2_SGD.lean`, `W2_SFTC.lean`, `W2_SFTD.lean` were created from it): a
  hunk anchored at Partial line `L` lands in Wave1 at `L` if `L ≤ 1301`, at `L + 1312` if `1301 < L ≤ 5564`, and at
  `L + 1329` if `L > 5565`.  `W2_SGD.lean`'s two hunks (`672a673,838`, `691c857,868` vs Partial) are both below 1301 and
  apply to `Wave1_Assembled.lean` at the SAME line numbers.  Diff wave-2 files against `Partial_Assembled.lean` (their
  base), not against `Statements_FINAL.lean`.

## 3. Remaining `sorry` and the assembler's own closure (task 3)

**The 9 `sorry` declarations, exactly** (assembled line of the `theorem`; `sorry` line in brackets):

| line | declaration | PLAN unit | wave | status |
|---|---|---|---|---|
| 679 [691] | `sg_daughters_products` | U103-D | **wave 2** | leaf open in wave 1. NOTE: `W2_SGD.lean` (18:20 UTC, `sgd_` block + 12-line body, report `W2_SGD_REPORT.md`) already proves it on top of `Partial_Assembled.lean`; its hunks rebase to Wave1 at identical line numbers (§2) |
| 5547 [5555] | `s7_sliding_law_at` | U110-E | **wave 2** | leaf open; inputs U110-A/B/C/D all adopted; the rotation equality `hr` (U_S7A_REPORT §2, "U110-A2") and `s7b_SlidingTransport.ret` (U_S7B_REPORT) are the two geometric inputs still to be produced |
| 6712 [6721] | `s7_bigon_law_at` | U110-K | **wave 3** | leaf open; waits on U110-F/J helpers and on the RI/RII question (§7) |
| 8443 [8448] | `sft_same_sign` | U112-C | **wave 2** | leaf open; `sfta_` helpers (U112-A) adopted, incl. `sfta_soft_data` and `sfta_InsertMarkTransport.cornerStateSum_transport` |
| 8596 [8601] | `sft_loop` | U112-D | **wave 2** | leaf open |
| 8691 [8692] | `cb_singleton` | §6 row theorem | — | waits for row 100 (`cb_singleton_of_floor thm_floor`) |
| 8696 [8697] | `corner_values` | §6 row theorem | — | waits for row 100 |
| 8701 [8702] | `thm_C_S7` | §6 row theorem | — | waits for row 100 |
| 8706 [8707] | `thm_C_soft` | §6 row theorem | — | waits for row 100 |

**Wave-2 units and what each still owes** (PLAN_FINAL §4 rows): U103-D `sg_daughters_products` (returned as
`W2_SGD.lean`, to be adopted by the wave-2 assembler); U110-E `s7_sliding_law_at`; U110-F (helper unit for the bigon
two-newborn sector, `B = (1−ε)J`, no leaf); U110-J (floor leaves for the bigon branch — its ONE frozen leaf,
`s7_corner_product`'s 2nd conjunct, is now CLOSED here, so U110-J owes only the `s7j_` helpers for U110-K: noninterlacing
rows zero, one-newborn rows via `hsing`, different-block rows; it must NOT re-prove `s7_corner_product` — the assembler
keeps the first body and reports a CONFLICT); U112-C `sft_same_sign`; U112-D `sft_loop`.
**Wave 3:** U110-K `s7_bigon_law_at` (assembly of F, G, H, I, J).  U110-K's proof must be placed AFTER U110-G's and
U110-H's blocks (U_S7H_REPORT §4): in the current layout H and I sit before `s7_bigon_law_at` and G after it, so K needs
either a `--move` of G's anchor above `s7_bigon_law_at` or to consume `s7g_` through forward references placed below the
two algebra leaves (frozen statements are unaffected either way).

**The assembler's own closure (≈ 15 min): `s7_corner_product`, 2nd conjunct.**  The frozen file proved the 1st conjunct
(`coeffAt_mul_eq_zero_of_lt_floor`) and left `coeffAt (k₁+k₂) 0 (f*g) = coeffAt k₁ 0 f * coeffAt k₂ 0 g` as `sorry`
(PLAN: U110-J).  It is a pure ring fact: the `(k₁+k₂, 0)` monomial of `f * g` is reached by exactly one pair of support
monomials, `(k₁,0) + (k₂,0)` — the `a`-floors `k₁ ≤ mindegAZ f ≤ a.1`, `k₂ ≤ mindegAZ g ≤ b.1` with `a.1 + b.1 = k₁ + k₂`
force `a.1 = k₁`, `b.1 = k₂`, and `hz₁`, `hz₂` (no negative `z`-exponents) with `a.2 + b.2 = 0` force `a.2 = b.2 = 0`; then
Mathlib's `AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd` (the device of the accepted `coeff_mul_of_max_weight`,
LinkLaurentRing.lean:695) gives the product.  18 tactic lines, INLINE in the leaf body (no helper, no new name), packaged
as the unit file **`U_S7J0.lean`** (= frozen file + hunk `505c505,522`, removed line `  sorry` only) so the assembler
pipeline stays reproducible.  Standalone probe: scratchpad `corner_product_probe.lean` (imports `SM.LinkLaurentRing`
only, 7 s, axioms `[propext, Classical.choice, Quot.sound]`).  This confirms the pre-review's note that `hz₁ hz₂` are
load-bearing (they are used exactly to kill the `(k₁+j, −j)`-type pairs).  No other open leaf is a small gap: the four
remaining unit leaves are each a full wave-2/3 unit (500-2200 lines in PLAN §4).

## 4. Compile, axioms (task 4)

`#print axioms` on a scratch copy of the assembled file (scratchpad `Wave1_axioms2.lean`, 0 errors, 22 s), 63 queries.
Union of axioms over the whole file: `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm,
SM.lp_lm_uniqueness` + `sorryAx` only through the 5 open leaves.  Fully proved, unconditional or hypothesis-form:

| declaration | axioms |
|---|---|
| `SM.corner_values_i` (row 105 (i), unconditional) | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |
| `SM.corner_values_of_singleton` | same six |
| `SM.cornerHomfly_ne_zero` | same six |
| `SM.sg_isolated_undominated` (leaf, U103-A) | `[propext, Classical.choice, Quot.sound]` |
| `SM.sg_daughters_rotation` (leaf, U103-E) | `[propext, Classical.choice, Quot.sound]` |
| `SM.s7_universal_extraction` (leaf, U110-G) | `[propext, Classical.choice, Quot.sound]` |
| `SM.s7_corner_product` (leaf, both conjuncts, U110-J/assembler) | `[propext, Classical.choice, Quot.sound]` |
| `SM.sft_mixed` (leaf, U112-B) | `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` |
| `SM.carrierUniformOrOneDissent_of_signed` (the bridge), `allLeftOrOneRight_of_signed`, `signedUniformOrOneDissent_of_uniform`, `coeffAt_mul_eq_zero_of_lt_floor`, `sg_slot_identity`, `cvl_embedded_of_no_crossings`, `CS7Data.contactSign_literal`, `sft_turn_ne_zero`, `sft_attachment_ne_zero` | `[propext, Classical.choice, Quot.sound]` (`sft_signType_cases`: `[propext]`; `sft_signType_neg_ne_zero`: none) |
| `SM.CS7Data.bigon/.sliding`, `CSoftData.exists_generic`, `CSoftData.doubled`, `CornerValuesData.embedded_rotationInt`, `FloorTheoremData.slot_le_of_signed` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` |
| sample helpers: `s7a_componentEquiv_owner`, `s7a_sliding_relocation_sign`, `s7b_slidingDecompositionEquiv`, `s7b_eligibleDecompositionEquiv`, `s7c_carrierWeight_interlacing`, `s7i_different_slot`, `sgb_pieceEquiv`, `sge_rotation_ray`, `s7g_extraction_of_skein` | `[propext, Classical.choice, Quot.sound]` |
| `sgc_blockPoly_eq_of_labels_eq`, `s7g_skein_at_positive`, `s7h_extraction_two_component` | `+ SM.lp_lm` |
| `s7d_cornerCoefficient_eq_of_cut` | `+ SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` |
| `sfta_InsertMarkTransport.cornerStateSum_transport`, `sftb_cornerStateSum_eq_zero_of_consecutive_opposite` | `+ SM.lit_homfly` |

With `sorryAx` (as expected, through the open leaves only): `sg_daughters_products`, `s7_sliding_law_at`,
`s7_bigon_law_at`, `sft_same_sign`, `sft_loop`, the row assemblies `cb_singleton_of_floor`, `corner_values_of_floor`,
`thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_soft_of_cornerValues`, `thm_C_soft_of_floor`, and the 4 §6 rows.  No closed
leaf and no helper depends on `sorryAx`; nothing depends on any axiom outside the policy list
(`work/lean/axiom-policy.json`: standard + literature `lit_homfly`, `lp_lm`, `lp_lm_uniqueness`).

## 5. Statement byte-identity (task 5)

`python3 tools/stmt_check.py Wave1_Assembled.lean`: for each of the 49 top-level declarations of `Statements_FINAL.lean`
(4 `def`, 5 `structure`, 39 `theorem`, 1 `example`) the statement text — preceding docstring, `omit … in`, declaration
line(s) through the signature's `:=` (a `structure`'s whole field block) — occurs byte-for-byte EXACTLY ONCE, in the
frozen order, and its name is declared exactly once: **49/49 PASS** (exit 0).  Independently, `diff` shows the only
removed frozen lines are the five `  sorry` (§2).

## 6. Name-clash scan (task 6)

Namespace-aware scan (namespaces tracked through `namespace … end`; `.lake` excluded) of the **578** new top-level
declarations of the assembled file against the **680** `.lean` files of `work/lean` (SM, CV, Bridge, RProof,
Supplemental): **0 full-name clashes**; **0 duplicated names inside the assembled file**; every new `SM.`-level name
carries its unit prefix (`sgb_` 31, `sgc_` 6, `sge_` 22, `sfta_` 114, `sftb_` 6, `s7a_` 91, `s7b_` 151, `s7c_` 49,
`s7d_` 27, `s7g_` 13, `s7h_` 19, `s7i_` 49); unprefixed short names live only inside unit namespaces
(`s7b_ReturnTransport.*`, `s7b_SupportSplit.*`, `s7b_PivotSplit.*`, `s7b_SlidingTransport.*`,
`sfta_InsertMarkTransport.*`, `sfta_IsInsertion.*`).  30 short-name coincidences across DIFFERENT namespaces
(`sfta_InsertMarkTransport.cornerStateSum_transport` vs `Carrier.MarkTransport.cornerStateSum_transport`, etc.) are
informational only — distinct full names, no shadowing (`open Carrier` is in force, but the unit names are always
written with their namespace or resolved inside it).  Known REDUNDANCIES with accepted lemmas not among the frozen
imports (different names, replace at port time): `sftb_markSuccessor_vertex_of_no_crossing` =
`Carrier.markSuccessor_vertex_of_no_crossing` (SM/CS5.lean:30); `s7c_carrierWeight_eq_cornerSelector` =
`carrierWeight_eq_cornerSelector` (SM/CS3.lean:1453).  Port hazard from the pre-review (FR-CC-15) still stands: §0
redeclares `SM.AllLeftOrOneRight` / `SM.CarrierUniformOrOneDissent` / `SM.FloorTheoremData` under the floor lane's
names and must be deleted when the floor module lands.

## 7. U110-G GO / NO-GO verdict (from U_S7G_REPORT §0, confirmed by the assembled state)

**SPLIT.**
* **GO** — `s7_universal_extraction` is PROVED (standard axioms) and the skein triple at the positive contact crossing is
  available at the RECORD level: `s7g_skein_at_positive` (`+ lp_lm`), `s7g_cornerHomfly_skein`, with the oriented
  smoothing's record identified with `D.record.smooth v` (`exists_smoothing_record_visit`).  The two glue lemmas
  `s7g_switch_value_of_rii` / `s7g_value_of_ri` take the R-II / R-I witnesses as HYPOTHESES, so the bigon branch is
  consumable the moment the witnesses exist.
* **NO-GO within budget** — the `RIIData` witness for the bigon `{x, y}` on `D_H.switch x` and the `RIData` witness for
  the curl `y` on `D_A`: no generic constructor exists in the accepted library (the only sites are the U6 front-word slot
  diagrams and `Curl.k2_ri`, the wrong shape); a Smoothing-style generic bigon-deletion constructor is estimated at
  6,000-10,000 lines / 80-120 h, 3-4× U110-G's whole budget.  Escape routes checked and closed (record-level RII =
  proving RII invariance of HOMFLY, against the literature-interface policy; front-word `P_typeII` only for cusp-adjacent
  patterns; skein tricks need RI).
* **Recommendation carried forward**: keep the leaf statements; schedule the witnesses as a separate lane
  ("RIIDeletion"), and AVOID the RI step by reading `D_A`'s component 1 as the positive lift of the half contact carrier
  of the enlarged support `T ∪ {x, y}` (sm-4:857-866) so that only the two-component row accounts for `y` as a self
  crossing of writhe +1 (`homflyrows.two_component_row`, `MarkedProducts.lean:323/381`) — U_S7H's
  `s7h_extraction_two_component` is already in the file for this.  Consequence for wave 3: `s7_bigon_law_at` (U110-K) is
  BLOCKED on the R-II deletion witness unless the executor accepts FINAL_REVIEW's honest sentence "110 sliding proved,
  bigon stated; the bigon route waits on a generic R-II deletion constructor (Smoothing-scale)".

## 8. Leaves reported false

**None.**  Every unit report (U_S7A §2, U_S7B, U_S7C, U_S7I, U_SFTB, U_SGA, U_SGB, U_SGC, W2_SGD) states "nothing
believed false / no missing hypothesis"; the pre-review's truth probes found all 10 leaves TRUE.  One strength noted by
the pre-review stands: `sg_daughters_rotation` does not assume isolation and is proved as stated.

## 9. Warnings (cosmetic; all pre-existing in `U_SFTA.lean`, none in frozen text)

14 non-sorry warnings, assembled lines 7131-8043 (U_SFTA block): 8 × `if_neg` deprecated (→ `ite_eq_right`), 4 ×
"automatically included section variable(s) unused" (`sfta_insert_next_att`, `sfta_markKey_visit_eq`, `sfta_soft_new_key`,
`sfta_soft_zero_keys`), 2 × unreferenced variable names `S`, `T` (line 7269).  To be cleaned when U112-A's report / U112-C
arrive.  Every other block, the assembler's leaf body included, compiles with 0 non-sorry warnings.

## 10. Notes for the executor

* Everything not listed in §3 is PROVED: the four row-level assemblies (hypothesis form), `corner_values_i`, the bridge,
  the companions, 5 of the 10 unit leaves, and 578 unit helpers (12 blocks, 7,890 lines).  The file is a draft under
  `work/drafts/`; nothing was written under `work/lean`.
* Wave-2 assembly: run `python3 tools/partial_assemble.py --out Wave2_Assembled.lean --units <the 14 above>,U_<new>…` for
  units written against `Statements_FINAL.lean`; for the `W2_*.lean` files written against `Partial_Assembled.lean`, extract
  their hunks vs Partial and apply with the rebase rule of §2 (or point the script's `BASE` at `Partial_Assembled.lean`
  for those units).  Then `stmt_check.py`, the compile, and `#print axioms` as above.
* Reproduce this file: `cd work/drafts/corner && python3 tools/partial_assemble.py --out Wave1_Assembled.lean --units
  U_SGA,U_SGB,U_SGC,U_SGE,U_SFTA,U_SFTB,U_S7A,U_S7B,U_S7C,U_S7D,U_S7G,U_S7H,U_S7I,U_S7J0 && python3 tools/stmt_check.py
  Wave1_Assembled.lean && cd ../../lean && lake env lean ../drafts/corner/Wave1_Assembled.lean`.
