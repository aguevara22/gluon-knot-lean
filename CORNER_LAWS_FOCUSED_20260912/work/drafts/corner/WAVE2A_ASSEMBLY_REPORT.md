# WAVE2A_ASSEMBLY_REPORT — corner chain, wave-2a assembly (2026-09-15 19:40 UTC / 3:40pm ET)

Assembler subagent (wave 2a).  Inputs: `Partial_Assembled.lean` (7390 lines, sha256 `85312954…081891`, the base the three
wave-2 units were written against), the three unit files `W2_SGD.lean` (`0fc6100a…1b8b2d`), `W2_SFTC.lean`
(`41540943…855ea`), `W2_SFTD.lean` (`7e412a93…086f6`) with their reports, and `Wave1_Assembled.lean` (8719 lines,
`a2064c2f…6b569a`, WAVE1_ASSEMBLY_REPORT.md), which supersedes `Partial_Assembled.lean` by exactly two verified-clean
hunks (the U_S7A helper block and the assembler's closure of `s7_corner_product`).  So that nothing already proved is
lost, the assembly is built on **`Partial_Assembled.lean` as the base with FOUR "units"**: `Wave1_Assembled` (its two
hunks vs Partial audited like any unit: `1301a1302,2613` = the U_S7A block, byte-identical to U_S7A's own hunk up to the
blank separator line; `5565c6877,6894` = U_S7J0's 18-line body, byte-identical; removed line `  sorry` only), `W2_SGD`,
`W2_SFTC`, `W2_SFTD`.

Output: **`work/drafts/corner/Wave2a_Assembled.lean`** — 12,233 lines, sha256
`3bd5a98c04682c81dbd54831aa4756d8104241b49aa478b2d2de84093e9b6802`, produced by
`python3 tools/wave2a_assemble.py` (defaults: `--base Partial_Assembled.lean --units Wave1_Assembled,W2_SGD,W2_SFTC,W2_SFTD
--out Wave2a_Assembled.lean`; summary JSON on stdout).  Nothing was written under `work/lean`.

**Mandated check:** `cd work/lean && lake env lean ../drafts/corner/Wave2a_Assembled.lean` — **0 errors**, exit 0, 24 s warm
(load ≈ 11 on 8 cores, one other prover's `lean` running).  27 warnings = **6 `declaration uses sorry`** (`s7_sliding_law_at`
5724, `s7_bigon_law_at` 6889, the four §6 rows 12205/12210/12215/12220) + 21 cosmetic (§9).
**`grep -c sorry Wave2a_Assembled.lean` = 8** = 6 sorry bodies + the 2 prose mentions inherited from the frozen file
(header line 25, §6 header line 12200).  No `#print`, `#eval`, `#check`, `set_option` anywhere in the file.

## 1. Diff audit of the units (task 1)

Method (`tools/wave2a_assemble.py`, the wave-1 script generalised with `--base`, a comment-aware declaration scanner,
per-unit expectations and an in-block token audit): every unit is `diff`ed against the base; a hunk is CLEAN iff it is a
pure insertion (a helper block), or a `c`-hunk whose REMOVED lines are exactly `  sorry` inside the body of THAT unit's own
PLAN_FINAL §4 leaf.  Additionally every inserted block is scanned: every top-level declaration must carry the unit's
prefix (or live in a namespace carrying it), and no `sorry`, `#print`, `#eval`, `#check`, `axiom`, `import`, `set_option`
may appear in added text.  Anything else is a VIOLATION → unit rejected.

| unit | PLAN row / leaf | hunks vs `Partial_Assembled.lean` | removed lines | block (decls) | body | verdict |
|---|---|---|---|---|---|---|
| `Wave1_Assembled` | U110-A block + U110-J0 body (`s7_corner_product`) | `1301a1302,2613`, `5565c6877,6894` | `  sorry` (5565) | 1312 lines, 91 `s7a_` decls | 18 lines | **clean, adopted** |
| `W2_SGD` | U103-D leaf `sg_daughters_products` + `sgd_` | `672a673,838`, `691c857,868` | `  sorry` (691) | 166 lines, 7 `sgd_` decls | 12 lines | **clean, adopted** |
| `W2_SFTC` | U112-C leaf `sft_same_sign` + `sftc_` | `7109a7110,7802`, `7119c7812,7865` | `  sorry` (7119) | 693 lines, 36 `sftc_` decls | 54 lines | **clean, adopted** |
| `W2_SFTD` | U112-D leaf `sft_loop` + `sftd_` | `7261a7262,9827`, `7272c9838,9863` | `  sorry` (7272) | 2566 lines, 188 `sftd_` / `sftd_LoopTransport.*` decls | 26 lines | **clean, adopted** |

**Violations: none.**  Each `c`-hunk sits in the body of the unit's own leaf (checked by scanning back to the enclosing
declaration); no statement, definition, structure, name, docstring or import of the frozen/partial file was changed; no
§6 row theorem touched; no import added by any unit; no forbidden token in any added text.  (The first run flagged a
`W2_SFTD` "declaration `is`" — a docstring prose line "The soft / instance is built from …" read at column 0; the scanner
was made comment-aware and the unit is clean.)  Every W2 report's self-description of its diff (`W2_SGD_REPORT`,
`W2_SFTC_REPORT` §0, `W2_SFTD_REPORT` §0) matches the observed hunks exactly.  `stmt_check.py` on each unit file: 49/49
(reported by the units; re-checked on the assembled file, §5).

## 2. Assembly (task 2)

`Wave2a_Assembled.lean` = `Partial_Assembled.lean` with all eight clean hunks applied: the four leaf bodies replaced in
place, the four helper blocks inserted verbatim and CONTIGUOUSLY at their own anchors (each block verified to occur as
ONE contiguous slice, exactly once):

| block | assembled lines | inside | anchor (as in the unit) |
|---|---|---|---|
| `W2_SGD` (`sgd_`, 7 decls) | 673-838 | `section Singleton` | after the `sgc_` block, before the docstring of `sg_daughters_products` (845) |
| `Wave1`/U_S7A (`s7a_`, 91 decls) | 1479-2790 | `section VertexEdge` | after `CS7Data.contactSign_literal`, before the U_S7B block |
| `W2_SFTC` (`sftc_`, 36 decls) | 8616-9308 | `section Soft` | after the U_SFTA block (7182-8613), before the docstring of `sft_same_sign` (9313) |
| `W2_SFTD` (`sftd_`, 188 decls) | 9514-12079 | `section Soft` | after the U_SFTB block (9373-9484) and `sft_mixed`, before the docstring of `sft_loop` (12085) |

Leaf bodies: `sg_daughters_products` 857-868, `s7_corner_product` 7054-7071, `sft_same_sign` 9318-9371, `sft_loop`
12090-12115.  The units' own `section … end`, `namespace … end`, `variable`, `omit … in` wrappers are kept verbatim; the
frozen `namespace SM` / `open Link Carrier` / `attribute [local instance] Classical.propDecidable` / `noncomputable
section` preamble still encloses everything (`end` 12231, `end SM` 12233).  **Import union**: nothing to add (all four
units use the 17 imports of `Partial_Assembled.lean`).  **De-duplication / rename-on-clash**: not exercised
(`dedup_dropped = []`, `renamed = []`; no declaration name occurs twice in the assembled file).  Order dependence: the
`sftd_` block uses `sfta_*` (U112-A) and `sftb_sub_one_ne` (U112-B) and `sge_*` (U103-E) — all placed above it in the
frozen order; the `sftc_` block uses `sfta_*` and `sge_*`; the `sgd_` block uses `sgb_*`/`sgc_*` (above it) and the leaf
`sg_isolated_undominated`.  Everything compiles in this order.

`diff Statements_FINAL.lean Wave2a_Assembled.lean` = `16a17 215c216,837 235c857,1233 256c1254,1280 454a1479,5720
467a5734,6880 488a6902,7037 494c7043 505c7054,7071 615a7182,9308 625c9318,9484 634c9493,12078 646c12090,12115`; the ONLY
removed frozen lines are **eight `  sorry`** (the 8 closed leaves).  `diff Wave1_Assembled.lean Wave2a_Assembled.lean` =
`672a673,838 691c857,868 8438a8616,9308 8448c9318,9371 8590a9514,12079 8601c12090,12115` (removed: three `  sorry`).
`diff Partial_Assembled.lean Wave2a_Assembled.lean` = the eight hunks of §1 (removed: four `  sorry`).

**Rebase rules for anything written against an earlier base.**  Partial line `L` → Wave2a: `L` if `L ≤ 672`; `+166` if
`≤ 691`; `+177` if `≤ 1301`; `+1489` if `≤ 5565`; `+1506` if `≤ 7109`; `+2199` if `≤ 7119`; `+2252` if `≤ 7261`; `+4818`
if `≤ 7272`; `+4843` beyond.  Wave1 line `L` → Wave2a: `L` if `L ≤ 672`; `+166` if `≤ 691`; `+177` if `≤ 8438`; `+870` if
`≤ 8448`; `+923` if `≤ 8590`; `+3489` if `≤ 8601`; `+3514` beyond.  (Checks: 7390+4843 = 8719+3514 = 12233.)  For the
NEXT assembler: `tools/wave2a_assemble.py --base <the base a unit was written against> --units <unit>` classifies any
unit; units with different bases are merged by running the script once per base and applying the content-located hunks,
or — simplest — by writing wave-2b units against `Wave2a_Assembled.lean` and running `--base Wave2a_Assembled.lean`.

## 3. Remaining `sorry` — the unproved leaves, exactly (task 3)

| assembled line | declaration | PLAN unit | status |
|---|---|---|---|
| 5724 [sorry 5732] | `s7_sliding_law_at` | U110-E (wave 2b) | OPEN.  Inputs now all present in the file: U110-A/B/C/D blocks; the geometric rotation equality `hr` is delivered by the late unit `W2_S7A2.lean` (§8, NOT adopted here); `s7b_SlidingTransport.ret` still to be produced (WAVE1 §3) |
| 6889 [sorry 6898] | `s7_bigon_law_at` | U110-K (wave 3) | OPEN; blocked on the R-II deletion witness (WAVE1 §7) |
| 12205 [12206] | `cb_singleton` | §6 row 103 | `sorry` by design in the draft; **closes as `cb_singleton_of_floor thm_floor`** — tested sorry-free in the port probe (§4) |
| 12210 [12211] | `corner_values` | §6 row 105 | idem, **`corner_values_of_floor thm_floor`** — sorry-free in the port probe |
| 12215 [12216] | `thm_C_S7` | §6 row 110 | `thm_C_S7_of_floor thm_floor` typechecks but inherits `sorryAx` from the two open leaves |
| 12220 [12221] | `thm_C_soft` | §6 row 112 | idem, **`thm_C_soft_of_floor thm_floor`** — sorry-free in the port probe |

Unit leaves: **8 of 10 PROVED** (`sg_isolated_undominated`, `sg_daughters_products`, `sg_daughters_rotation`,
`s7_universal_extraction`, `s7_corner_product`, `sft_same_sign`, `sft_mixed`, `sft_loop`); rows 103, 105, 112 are
complete modulo the row-100 composition.  **Own proving (≤ 45 min budget): not attempted** — neither open leaf is a
small gap (U110-E is a full unit whose second input `s7b_SlidingTransport.ret` does not exist yet; U110-K is blocked on
a Smoothing-scale constructor), and the §6 rows are not gaps but the deliberate port-time compositions, which I tested
instead (§4).  The four W2/W1 reports each state "nothing believed false / no missing hypothesis"; nothing here
contradicts them.

## 4. Compile, axioms, and the row-closing compositions (task 4)

**Exhaustive `#print axioms`** (scratch copy `Wave2a_axioms.lean` in the scratchpad = the assembled file + one
`#print axioms` per declaration, 857 queries, 0 errors, 26 s; parsed prime-tolerantly, 857/857 printed).  Axiom union
over the whole file: `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — all in
`work/lean/axiom-policy.json` (standard + literature) — plus `sorryAx` in EXACTLY these 8 declarations:
`s7_sliding_law_at`, `s7_bigon_law_at`, `thm_C_S7_of`, `thm_C_S7_of_floor`, `cb_singleton`, `corner_values`, `thm_C_S7`,
`thm_C_soft` (the last four only because their draft bodies are `sorry`).  No helper of any unit depends on `sorryAx`.

| declaration (all `SM.`) | axioms |
|---|---|
| `cb_singleton_of_floor` (row 103 ← thm:floor) | `[propext, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness]` — **sorry-free (new in wave 2a)** |
| `corner_values_i` (row 105 (i), unconditional), `corner_values_of_singleton`, `corner_values_of_floor` | same six — `_of_singleton`/`_of_floor` **sorry-free (new)** |
| `thm_C_soft_of_cornerValues`, `thm_C_soft_of_floor` (row 112 ← 105 ← 100) | same six — **sorry-free (new)** |
| `thm_C_S7_of`, `thm_C_S7_of_floor` | `+ sorryAx` (through the two open leaves) |
| leaves `sg_daughters_products`, `sft_same_sign`, `sft_loop` | the six policy axioms, no `sorryAx` |
| leaves `sg_isolated_undominated`, `sg_daughters_rotation`, `s7_universal_extraction`, `s7_corner_product` | `[propext, Classical.choice, Quot.sound]` |
| leaf `sft_mixed` | `+ lit_homfly` |
| bridge `carrierUniformOrOneDissent_of_signed`, `allLeftOrOneRight_of_signed`, `signedUniformOrOneDissent_of_uniform`, `sg_slot_identity`, `coeffAt_mul_eq_zero_of_lt_floor` | `[propext, Classical.choice, Quot.sound]` |
| `FloorTheoremData.slot_le_of_signed`, `CS7Data.bigon/.sliding`, `CSoftData.exists_generic/.doubled`, `CornerValuesData.embedded_rotationInt` | `+ lit_homfly` |
| new helpers: `sgd_daughters` std; `sgd_blocksOwnedBy_eq`, `sgd_carrierPoly_eq`, `sgd_carrierCrossingCount_eq`, `sgd_exists_preimage` `+ lp_lm`; `sftc_homfly_eq` six; `sftc_rotation_eventually`, `sftc_principalAngle_add` std; `sftd_LoopTransport.cornerStateSum_transport`, `.homfly_residual`, `.sum_transport`, `.cornerProduct_supportY`, `.cornerCoefficient_tri`, `sftd_loopTransport_homfly` six; `.cornerProduct_support_eq_zero`, `.cornerCoefficient_residual` `+ lit_homfly`; `sftd_residual_rotation_bound`, `sftd_loopTransport`, `sftd_sign_arith` std | (per-prefix totals: `sgd_` 7 = 3 std + 4 `+lp_lm`; `sftc_` 36 = 35 std-or-less + 1 six; `sftd_` 188 = 180 std-or-less + 6 six + 2 `+lit_homfly`) |

**Shape identity of the §0 copy vs the accepted interface.**  The 32-line span `AllLeftOrOneRight` / `CarrierUniformOrOneDissent` /
`FloorTheoremData` (docstrings included; assembled lines 60-91) is **byte-identical** (`cmp`) to
`work/lean/SM/CarrierFloor.lean:377-408` (inside `namespace SM`, `section Floor`, `open Carrier`).  Consequence, as the
task anticipated: with `import SM.CarrierFloorRows` present the copy is a DUPLICATE `SM.FloorTheoremData` and the file
does not compile; with the copy deleted the names resolve to the accepted ones and every consumer typechecks unchanged.
`SM.thm_floor : FloorTheoremData` (SM/CarrierFloorRows.lean:13, `thm_floor_of_bound transverseFrontBound`) has axioms
`[propext, Classical.choice, Quot.sound, lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word,
src_contact]` — all registered in `axiom-policy.json` (`literature`).

**Port probe** (`work/drafts/corner/Wave2a_PortProbe.lean`, 12,225 lines, sha256 `ce4a3cbf…bd68`; a probe, not an
assembly product): the assembled file with (i) lines 60-92 deleted (the three copies + trailing blank; a 2-line note left
in their place), (ii) `import SM.CarrierFloorRows` appended to the 17-line import header, (iii) the four §6 bodies
replaced by `cb_singleton_of_floor thm_floor`, `corner_values_of_floor thm_floor`, `thm_C_S7_of_floor thm_floor`,
`thm_C_soft_of_floor thm_floor`, (iv) `#print axioms` of the rows and an `example : CbSingletonData ∧ CornerValuesData ∧
CSoftData := ⟨cb_singleton, corner_values, thm_C_soft⟩` before `end SM`.  `cd work/lean && lake env lean
../drafts/corner/Wave2a_PortProbe.lean`: **0 errors**, 26 s, 23 warnings = 2 `declaration uses sorry` (`s7_sliding_law_at`,
`s7_bigon_law_at` only) + the same 21 cosmetics.  Axioms:

| row theorem (composition) | axioms |
|---|---|
| `SM.cb_singleton := cb_singleton_of_floor thm_floor` (row 103) | `[propext, Classical.choice, Quot.sound, lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact]` — **registered only, no `sorryAx`** |
| `SM.corner_values := corner_values_of_floor thm_floor` (row 105) | same nine — **no `sorryAx`** |
| `SM.thm_C_soft := thm_C_soft_of_floor thm_floor` (row 112, fixed target name) | same nine — **no `sorryAx`** |
| `SM.thm_C_S7 := thm_C_S7_of_floor thm_floor` (row 110) | same nine `+ sorryAx` (typechecks; not portable) |

The full import closure of `SM.CarrierFloorRows` (`SM.CarrierFloor` ← `SM.Curl`, `SM.TransverseFront`,
`SM.CeSmoothingRecord`, `SM.CornerStateSum`, `SM.LinkPositiveLift`, `SM.UniformRotation`, `SM.FdContactUnits`) introduces
no ambiguity or error anywhere in the 12k lines — the probe is the evidence.  (First probe attempt failed for a reason
worth recording: assembled line 9375 is a docstring prose line at column 0 beginning `import closure; …`, so a naive
"insert after the last `^import` line" put the import mid-file; header insertion must use the contiguous run of imports
from line 1.  The same hazard exists for `^structure` (line 2798, a prose line "structure `s7b_SlidingTransport` whose one
field…") and `^instance` (an `sftd_` docstring line) — harmless to Lean, hostile to line-anchored tools.)

## 5. Statement byte-identity (task 5)

`python3 tools/stmt_check.py Wave2a_Assembled.lean`: for each of the 49 top-level declarations of `Statements_FINAL.lean`
(4 `def`, 5 `structure`, 39 `theorem`, 1 `example`) the statement text (preceding docstring, `omit … in`, declaration
line(s) through the signature's `:=`; a `structure`'s whole field block) occurs byte-for-byte EXACTLY ONCE, in the frozen
order, and the name is declared exactly once: **49/49 PASS** (exit 0).  Independently, `diff` shows the only removed
frozen lines are the eight `  sorry` (§2).  The §0 copy is also byte-identical to the accepted module (§4).

## 6. Name-clash scan (task 6)

`tools/clash_scan.py Wave2a_Assembled.lean` (new; namespace-aware, `namespace … end` tracked with dotted namespaces split,
comment lines skipped, `.lake` excluded) over the **680** `.lean` files / **19,646** declarations of `work/lean`:
**809 new declarations** in the assembled file (578 wave-1 + 7 `sgd_` + 36 `sftc_` + 188 `sftd_`), **0 full-name
clashes**, **0 duplicated names inside the file**.  Prefix statistics (every new `SM.`-level name carries its unit prefix;
unprefixed short names live only inside prefixed namespaces): `sgb_` 31, `sgc_` 6, `sgd_` 7, `sge_` 22, `s7a_` 91, `s7b_`
151, `s7c_` 49, `s7d_` 27, `s7g_` 13, `s7h_` 19, `s7i_` 49, `sfta_` 114, `sftb_` 6, `sftc_` 36, `sftd_` 188.
42 short-name coincidences in DIFFERENT namespaces — informational, distinct full names, no shadowing: the 30 of wave 1
(`s7b_ReturnTransport.{sameCycle_iff,cycleMap,cycleMap_mk,cycleEquiv,cycleEquiv_mk}` vs `Link.RecordIso`/`FrontRows.U2`;
`sfta_InsertMarkTransport.*` vs `Carrier.MarkTransport.*`/`GeoCarrier.GeoMarkTransport.*`; `sfta_IsInsertion.filter` vs
`Cycle.filter`) plus 12 new ones from `sftd_LoopTransport.{toMark, toMark_inl, toMark_inr, twin_eq, support,
mem_support, support_card, support_injective, leftTurns_transport, cornerStateSum_transport}` vs `Carrier.MarkTransport.*`
/ `GeoCarrier.GeoMarkTransport.*`, `sftd_LoopTransport.visit_fst_eq_iff` vs `Link.Diagram.visit_fst_eq_iff`,
`sftd_LoopTransport.residual` vs `RProof.LocalTable.residual`.  `open Carrier` is in force in the file, but these unit
names are always written qualified (`τ.toMark`, `sftd_LoopTransport.…`) or resolved inside their own namespace; the
compile confirms no ambiguity, also under the enlarged closure of the port probe.
Known REDUNDANCIES with accepted lemmas (different names, no clash; replace or keep at port): `sftb_markSuccessor_vertex_of_no_crossing`
= `Carrier.markSuccessor_vertex_of_no_crossing` (SM/CS5.lean:30); `s7c_carrierWeight_eq_cornerSelector` =
`carrierWeight_eq_cornerSelector` (SM/CS3.lean:1453); `sftc_regularPair_of_det_ne_zero` = `regularPair_of_det_ne_zero`
(SM/SoftRotation.lean:73); `sftc_softOldIndex_pred/_succ_pred`, `sftc_softNewIndex_pred` = SM/SoftRotation.lean:127/133/137
(SoftRotation is NOT in the import closure — keep the copies or add the import); in-file duplicates by design
(`sftc_signType_cases` = `sft_signType_cases` 12132, `sftc_sub_one_ne` = `sftb_sub_one_ne`, `sftc_soft_data` ⊃
`sfta_soft_data`) because the frozen file places the originals BELOW their consumer.

## 7. Port plan (task 7)

Precedent: the floor lane (`SM/CarrierFloor.lean` = statements + units + conditional assemblies in one module, 3,822
lines; `SM/CarrierFloorRows.lean` = the 15-line rows module).  Here the task's two-module split plus one module per row:

**(a) `SM/CornerChainStatements.lean`** (≈ 330 lines, sorry-free, no unit code).  Imports: the 17 frozen imports
(`SM.CBProducts … SM.VertexSides`) **plus `import SM.CarrierFloor`** (for `FloorTheoremData`, `AllLeftOrOneRight`,
`CarrierUniformOrOneDissent`).  Preamble as frozen: `namespace SM`, `open Link Carrier`, `attribute [local instance]
Classical.propDecidable` (file-local — must be repeated in EVERY module below), `noncomputable section`.  Content, in
frozen order: §0 **without lines 60-92** (the three copies: DELETE) — i.e. `section Floor` / `variable {n : ℕ} [NeZero n]`
+ the bridge `SignedUniformOrOneDissent`, `allLeftOrOneRight_of_signed`, `carrierUniformOrOneDissent_of_signed`,
`signedUniformOrOneDissent_of_uniform`, `FloorTheoremData.slot_le_of_signed` (93-150; the last now extends the ACCEPTED
structure's namespace — no clash, §6); §1 `section Algebra` (153-180); the four data structures with their companions,
each in its own `section` with the frozen `variable`s: `CbSingletonData` (184-201), `CornerValuesData` +
`CornerValuesData.embedded_rotationInt` (1319-1345 and 1397-1406), `CS7Data` + `.bigon` + `.sliding` +
`.contactSign_literal` (1420-1478), `CSoftData` + `.exists_generic` + `.doubled` (7109-7159 of §5's head: `open
SoftDuplication` 7111, structure 7123, companions through 7159).  Header docstring: rewrite lines 19-43 (drop the "Every `sorry` is either…" sentence, line
25, and the "§0 is a VERBATIM copy … to be deleted" paragraph, lines 37-43 → "§0 imports the accepted interface
SM/CarrierFloor.lean §7 and adds the signed-form bridge"); reword the §0 header 53-54 likewise.

**(b) `SM/CornerChainUnits.lean`** (≈ 11,700 lines, sorry-free; imports `SM.CornerChainStatements`).  Same preamble.
Content = the assembled file's §2-§5 minus what (a) took and minus the row-110 open material, in frozen order (the
`sftd_`/`sftc_` blocks use `sge_` from §2, so §2 must precede §5):
* §2 `section Singleton` (184-1315 minus `CbSingletonData`): `sg_isolated_undominated` (209), `sgb_` 260-602, `sgc_`
  603-672, `sgd_` 673-838, `sg_daughters_products` (845), `sge_` 870-1234, `sg_daughters_rotation` (1241),
  `sg_slot_identity` (1288), `cb_singleton_of_floor` (1301).
* §3 `section CornerValues` (1319-1416 minus the structure/companion): `cvl_embedded_of_no_crossings` (1347),
  `corner_values_i` (1374), `corner_values_of_singleton` (1408), `corner_values_of_floor` (1413).
* §4 `section VertexEdge` (1420-7105 minus `CS7Data` + companions): the helper blocks `s7a_` 1479-2790, `s7b_` 2791-4503,
  `s7c_` 4505-5170, `s7d_` 5171-5720, `s7h_` 5734-6048, `s7i_` 6049-6880, `s7g_` 6902-7037, and the two closed algebra
  leaves `s7_universal_extraction` (7040) and `s7_corner_product` (7048); **EXCLUDE** `s7_sliding_law_at` (5721-5732,
  docstring included), `s7_bigon_law_at` (6881-6898), `thm_C_S7_of` (7073-7098), `thm_C_S7_of_floor` (7100-7103) — they
  stay in the draft until wave 2b/3 closes them (then a `SM/CS7.lean` row module, fixed name `SM.thm_C_S7`).  Nothing in
  the helper blocks references the excluded declarations (only docstrings mention them).  Alternative: defer the whole
  §4 helper corpus (5,600 lines) to the row-110 port, keeping (b) at ≈ 6,100 lines now.
* §5 `section Soft` (7109-12198 minus `CSoftData` + companions): `sft_turn_ne_zero` (7165), `sfta_` 7182-8613, `sftc_`
  8616-9308, `sft_same_sign` (9313), `sftb_` 9373-9484, `sft_mixed` (9489), `sftd_` 9514-12079, `sft_loop` (12085),
  `sft_signType_neg_ne_zero`, `sft_attachment_ne_zero`, `sft_signType_cases` (12121-12137), `thm_C_soft_of_cornerValues`
  (12139), `thm_C_soft_of_floor` (12195).
If (b) is felt too large for one module, split at the frozen section boundaries into `SM/CornerChainSingleton.lean` (§2+§3),
`SM/CornerChainVertexEdge.lean` (§4), `SM/CornerChainSoft.lean` (§5, imports Singleton for `sge_`) — the compile is 24 s
for the whole file, so a single module is also fine.

**(c) Row modules** (each ≈ 15 lines, pattern of `SM/CarrierFloorRows.lean`; imports `SM.CornerChainUnits` and
`SM.CarrierFloorRows`; same preamble is NOT needed — plain `namespace SM … end SM`):
* `SM/CBSingleton.lean` — row 103: `theorem cb_singleton : CbSingletonData := cb_singleton_of_floor thm_floor` (proposed
  name; docstring from 12204).
* `SM/CornerValues.lean` — row 105: `theorem corner_values : CornerValuesData := corner_values_of_floor thm_floor`
  (clause (i) is `corner_values_i`, unconditional).
* `SM/CSoft.lean` — row 112, FIXED target name: `theorem thm_C_soft : CSoftData := thm_C_soft_of_floor thm_floor`; optionally
  the §7 consumer check as `example : CbSingletonData ∧ CornerValuesData ∧ CSoftData := ⟨cb_singleton, corner_values,
  thm_C_soft⟩` (the frozen `example` 12228-12229 uses `thm_C_S7_of_floor` and must be dropped or reduced this way).
Expected axioms of all three: the nine of §4 (registered only).  Row 110 (`thm_C_S7`) is NOT ported (D-F11/D-F14).

**Lines to delete / reword at port** (assembled numbering): DELETE 60-92 (the §0 copies); REWORD 19-43 (header; `sorry`
at 25), 53-54 (§0 header "VERBATIM … to be deleted"), 12200-12203 (§6 header, `sorry` at 12200); the `sorry` BODIES
12206/12211/12221 become the one-liners of (c), 12216 (`thm_C_S7`) is excluded with 5732/6898; the frozen `example`
12228-12229 dropped/reworded.  No `#print`/`#eval`/`#check` exists in the assembled file (only the two probe files carry
`#print axioms`, and they are not port products).  Docstring cross-references to "U_*_REPORT.md", "PLAN_FINAL", "wave"
are cosmetic; the executor's checker decides whether to strip them.

**Cosmetic warnings to clean at port (21, none in frozen text)**: 14 pre-existing in the `sfta_` block (WAVE1 §9: 8 ×
`if_neg` deprecated → `ite_eq_right`, lines 8046-8220 region; 4 × unused section variable; 2 × unreferenced `S`, `T` at
7446) and **7 new in the `sftd_` block** (W2_SFTD_REPORT claimed none): 10078:64/66 unreferenced `S`, `T` in
`sftd_LoopTransport.support_injective` (same pattern as sfta's 7446); 10937 / 10943 unused section variable `hP` in
`sftd_soft_key_a` / `sftd_soft_key_b` (add `omit hP in`); 10977 / 11018 `push_neg` deprecated → `push Not`; 12033:52
unreferenced `hS` in `sftd_residual_rotation_bound`'s statement (rename `_hS`; it is a binder of the ∀, so the statement of
the HELPER changes, not of any frozen declaration).

**Per-declaration destination of the 49 frozen declarations:**

| # | frozen declaration | kind | Statements_FINAL | Wave2a | port destination |
|---|---|---|---|---|---|
| 1 | `AllLeftOrOneRight` | def | 61 | 62 | **DELETE** (resolves to SM/CarrierFloor.lean §7 via `import SM.CarrierFloor`) |
| 2 | `CarrierUniformOrOneDissent` | def | 67 | 68 | **DELETE** (resolves to SM/CarrierFloor.lean §7 via `import SM.CarrierFloor`) |
| 3 | `FloorTheoremData` | structure | 78 | 79 | **DELETE** (resolves to SM/CarrierFloor.lean §7 via `import SM.CarrierFloor`) |
| 4 | `SignedUniformOrOneDissent` | def | 98 | 99 | `SM/CornerChainStatements.lean` |
| 5 | `allLeftOrOneRight_of_signed` | theorem | 102 | 103 | `SM/CornerChainStatements.lean` |
| 6 | `carrierUniformOrOneDissent_of_signed` | theorem | 130 | 131 | `SM/CornerChainStatements.lean` |
| 7 | `signedUniformOrOneDissent_of_uniform` | theorem | 137 | 138 | `SM/CornerChainStatements.lean` |
| 8 | `FloorTheoremData.slot_le_of_signed` | theorem | 144 | 145 | `SM/CornerChainStatements.lean` |
| 9 | `cornerHomfly_ne_zero` | theorem | 160 | 161 | `SM/CornerChainStatements.lean` |
| 10 | `coeffAt_mul_eq_zero_of_lt_floor` | theorem | 171 | 172 | `SM/CornerChainStatements.lean` |
| 11 | `CbSingletonData` | structure | 194 | 195 | `SM/CornerChainStatements.lean` |
| 12 | `sg_isolated_undominated` | theorem | 208 | 209 | `SM/CornerChainUnits.lean` |
| 13 | `sg_daughters_products` | theorem | 223 | 845 | `SM/CornerChainUnits.lean` |
| 14 | `sg_daughters_rotation` | theorem | 243 | 1241 | `SM/CornerChainUnits.lean` |
| 15 | `sg_slot_identity` | theorem | 264 | 1288 | `SM/CornerChainUnits.lean` |
| 16 | `cb_singleton_of_floor` | theorem | 277 | 1301 | `SM/CornerChainUnits.lean` |
| 17 | `CornerValuesData` | structure | 307 | 1331 | `SM/CornerChainStatements.lean` |
| 18 | `cvl_embedded_of_no_crossings` | theorem | 324 | 1348 | `SM/CornerChainUnits.lean` |
| 19 | `corner_values_i` | theorem | 350 | 1374 | `SM/CornerChainUnits.lean` |
| 20 | `CornerValuesData.embedded_rotationInt` | theorem | 374 | 1398 | `SM/CornerChainStatements.lean` |
| 21 | `corner_values_of_singleton` | theorem | 384 | 1408 | `SM/CornerChainUnits.lean` |
| 22 | `corner_values_of_floor` | theorem | 389 | 1413 | `SM/CornerChainUnits.lean` |
| 23 | `CS7Data` | structure | 412 | 1436 | `SM/CornerChainStatements.lean` |
| 24 | `CS7Data.bigon` | theorem | 424 | 1448 | `SM/CornerChainStatements.lean` |
| 25 | `CS7Data.sliding` | theorem | 435 | 1459 | `SM/CornerChainStatements.lean` |
| 26 | `CS7Data.contactSign_literal` | theorem | 447 | 1471 | `SM/CornerChainStatements.lean` |
| 27 | `s7_sliding_law_at` | theorem | 458 | 5724 | **NOT PORTED** (row 110 open; stays in the draft) |
| 28 | `s7_bigon_law_at` | theorem | 476 | 6889 | **NOT PORTED** (row 110 open; stays in the draft) |
| 29 | `s7_universal_extraction` | theorem | 491 | 7040 | `SM/CornerChainUnits.lean` |
| 30 | `s7_corner_product` | theorem | 499 | 7048 | `SM/CornerChainUnits.lean` |
| 31 | `thm_C_S7_of` | theorem | 511 | 7077 | **NOT PORTED** (row 110 open; stays in the draft) |
| 32 | `thm_C_S7_of_floor` | theorem | 536 | 7102 | **NOT PORTED** (row 110 open; stays in the draft) |
| 33 | `CSoftData` | structure | 557 | 7123 | `SM/CornerChainStatements.lean` |
| 34 | `CSoftData.exists_generic` | theorem | 566 | 7132 | `SM/CornerChainStatements.lean` |
| 35 | `CSoftData.doubled` | theorem | 580 | 7146 | `SM/CornerChainStatements.lean` |
| 36 | `sft_turn_ne_zero` | theorem | 599 | 7165 | `SM/CornerChainUnits.lean` |
| 37 | `sft_same_sign` | theorem | 620 | 9313 | `SM/CornerChainUnits.lean` |
| 38 | `sft_mixed` | theorem | 630 | 9489 | `SM/CornerChainUnits.lean` |
| 39 | `sft_loop` | theorem | 641 | 12085 | `SM/CornerChainUnits.lean` |
| 40 | `sft_signType_neg_ne_zero` | theorem | 652 | 12121 | `SM/CornerChainUnits.lean` |
| 41 | `sft_attachment_ne_zero` | theorem | 656 | 12125 | `SM/CornerChainUnits.lean` |
| 42 | `sft_signType_cases` | theorem | 663 | 12132 | `SM/CornerChainUnits.lean` |
| 43 | `thm_C_soft_of_cornerValues` | theorem | 670 | 12139 | `SM/CornerChainUnits.lean` |
| 44 | `thm_C_soft_of_floor` | theorem | 726 | 12195 | `SM/CornerChainUnits.lean` |
| 45 | `cb_singleton` | theorem | 736 | 12205 | `SM/CBSingleton.lean` (row 103) — body `cb_singleton_of_floor thm_floor` |
| 46 | `corner_values` | theorem | 741 | 12210 | `SM/CornerValues.lean` (row 105) — body `corner_values_of_floor thm_floor` |
| 47 | `thm_C_S7` | theorem | 746 | 12215 | **NOT PORTED** (row 110 open; stays in the draft) |
| 48 | `thm_C_soft` | theorem | 751 | 12220 | `SM/CSoft.lean` (row 112) — body `thm_C_soft_of_floor thm_floor` |
| 49 | `example@759` | example | 759 | 12228 | DROP, or reword to `⟨cb_singleton, corner_values, thm_C_soft⟩` in `SM/CSoft.lean` |

## 8. The late unit `W2_S7A2.lean` (NOT adopted — not among this task's inputs)

`W2_S7A2.lean` + `W2_S7A2_REPORT.md` landed at 19:26/19:28 UTC (3:26pm ET), while this assembly was running: unit S7A2
(prefix `s7a2_`, the rotation equality `hr` for U110-E), written against `Wave1_Assembled.lean`.  Audited with the same
script (`--base Wave1_Assembled.lean --units W2_S7A2`, output to the scratchpad only): ONE pure insertion `5543a5544,6257`
(714 lines, 60 declarations by the scanner — the report says 50 — all `s7a2_`-prefixed), 0 removed lines, no leaf body,
no forbidden token → **classifies CLEAN**; it would land in `Wave2a_Assembled.lean` after line 5720 (= 5543 + 177,
immediately before the docstring of `s7_sliding_law_at`, inside `section VertexEdge`, after the `s7d_` block).  Not
compiled together with this assembly (mandate: SGD/SFTC/SFTD); the wave-2b assembler should adopt it with U110-E.

## 9. Warnings summary

27 total: 6 `declaration uses sorry` (§3) + 21 cosmetic (§7, last paragraph).  The `sgd_`, `sftc_`, `s7a_` blocks and all
four new leaf bodies compile with 0 non-sorry warnings.

## 10. Reproduce

```
cd work/drafts/corner
python3 tools/wave2a_assemble.py            # → Wave2a_Assembled.lean (defaults: base Partial_Assembled.lean; units Wave1_Assembled,W2_SGD,W2_SFTC,W2_SFTD)
python3 tools/stmt_check.py Wave2a_Assembled.lean        # 49/49 PASS
python3 tools/clash_scan.py Wave2a_Assembled.lean        # 0 clashes
cd ../../lean && lake env lean ../drafts/corner/Wave2a_Assembled.lean   # 0 errors, 24 s
lake env lean ../drafts/corner/Wave2a_PortProbe.lean                    # 0 errors, rows 103/105/112 sorry-free
```
Scratchpad (session-local) artefacts: `Wave2a_axioms.lean` + `axioms_wave2a.log` (857 `#print axioms`),
`compile_wave2a.log`, `portprobe.log`, `clash_scan.json`, `wave2a_assemble.json`, `s7a2_audit.json`.
