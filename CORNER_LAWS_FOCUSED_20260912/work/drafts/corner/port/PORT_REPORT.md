# PORT_REPORT — corner chain lane, port of rows 103 cb:singleton, 105 lem:corner-values, 112 thm:C-soft (2026-09-15 19:57 UTC / 3:57pm ET)

Porter subagent.  Source: `work/drafts/corner/Wave2a_Assembled.lean` (12,233 lines, sha256
`3bd5a98c04682c81dbd54831aa4756d8104241b49aa478b2d2de84093e9b6802`), plan: `WAVE2A_ASSEMBLY_REPORT.md` §7 (the 49-row
table), probe: `Wave2a_PortProbe.lean`.  Nothing was written under `work/lean`; every compile used the scratch `.olean`
recipe of `work/drafts/cvtail/port/PORT_REPORT.md` §8.5 (§7 below).  Output, all under `work/drafts/corner/port/`:

| module | lines | sha256 | assembled source lines (verbatim) | compile |
|---|---|---|---|---|
| `SM/CornerChainStatements.lean` | 330 | `33f493ae…241d48` | 1-17 (+ `import SM.CarrierFloor`), 18, 44-52, 55-59, 93-202, 1315-1342, 1397-1406, 1416-1474, 7105-7159, 12198-12199, 12231-12233 | 0 errors, 0 warnings (plain `lake env lean` 13 s; `-o` 21 s) |
| `SM/CornerChainUnits.lean` | 11,842 | `fb391bbb…fef3b7` | 44-52, 182-187, 203-1322, 1343-1396, 1407-1423, 1475-5720, 5734-6880, 6900-7072, 7105-7114, 7160-12199, 12231-12233 | 0 errors, 21 cosmetic warnings (`-o` 33 s at load ≈ 11.5) |
| `SM/CBSingleton.lean` (row 103) | 14 | `a6eeced7…4f6a` | statement line 12205 | 0 errors, 0 warnings (21 s) |
| `SM/CornerValues.lean` (row 105) | 14 | `3ae40295…e6292` | statement line 12210 | 0 errors, 0 warnings (24 s) |
| `SM/CSoft.lean` (row 112, FIXED name `SM.thm_C_soft`) | 24 | `d7a5da09…6c02b` | statement line 12220; §7 heading 12223-12227 | 0 errors, 0 warnings (21 s) |

`grep -c sorry` = 0 in every module; no `#print`, `#eval`, `#check`, `set_option`, `axiom`, `admit` anywhere (the two prose
mentions of the frozen file, lines 25 and 12200, are in the reworded / omitted text).  Header line 1 of every module follows
the executor's template with the placeholder `<HH:MM>Z`.  `CornerChainUnits.lean` was NOT split (33 s compile).

## 1. What went where (the 49 frozen declarations + 809 helpers)

Coverage of the assembled file by the two big modules (script `tools/port_build.py`, every range boundary guarded by an
assertion on the expected text): the ONLY assembled lines in neither module are **19-43** (module docstring → reworded in
Statements), **53-54** (§0 heading → reworded), **60-92** (the three §0 copies `AllLeftOrOneRight`,
`CarrierUniformOrOneDissent`, `FloorTheoremData` + trailing blank — DELETED; byte-identical to `work/lean/SM/CarrierFloor.lean:377-408`
per WAVE2A §4, resolved through the added `import SM.CarrierFloor`), **5721-5733** (`s7_sliding_law_at` + docstring + blank),
**6881-6899** (`s7_bigon_law_at`), **7073-7104** (`thm_C_S7_of`, `thm_C_S7_of_floor`), **12200-12230** (§6 row theorems, §7
example).  Lines placed in BOTH modules (the wrappers, verbatim): 44-52 (preamble `namespace SM` / `open Link Carrier` /
`attribute [local instance] Classical.propDecidable` / `noncomputable section`), 182-187, 1315-1322, 1416-1423, 7105-7114,
12198-12199, 12231-12233 (the §2-§5 headings, `section`/`variable`/`open SoftDuplication` openers and the `end` closers).

* **Statements** (17 declarations): §0 bridge `SignedUniformOrOneDissent`, `allLeftOrOneRight_of_signed`,
  `carrierUniformOrOneDissent_of_signed`, `signedUniformOrOneDissent_of_uniform`, `FloorTheoremData.slot_le_of_signed`
  (93-150, now extending the ACCEPTED structure's namespace); §1 `cornerHomfly_ne_zero`, `coeffAt_mul_eq_zero_of_lt_floor`;
  `CbSingletonData`; `CornerValuesData`, `CornerValuesData.embedded_rotationInt`; `CS7Data`, `.bigon`, `.sliding`,
  `.contactSign_literal`; `CSoftData`, `.exists_generic`, `.doubled` — each inside its frozen `section` + `variable {n : ℕ} [NeZero n]`
  (§5 also `open SoftDuplication`).
* **Units** (829 declarations, frozen order; imports only `SM.CornerChainStatements`, which carries the 17 frozen imports):
  §2 `sg_isolated_undominated`, `sgb_` (31), `sgc_` (6), `sgd_` (7), `sg_daughters_products`, `sge_` (22), `sg_daughters_rotation`,
  `sg_slot_identity`, `cb_singleton_of_floor`; §3 `cvl_embedded_of_no_crossings`, `corner_values_i`, `corner_values_of_singleton`,
  `corner_values_of_floor`; §4 `s7a_` (91), `s7b_` (151), `s7c_` (49), `s7d_` (27), `s7h_` (19), `s7i_` (49), `s7g_` (13),
  `s7_universal_extraction`, `s7_corner_product`; §5 `sft_turn_ne_zero`, `sfta_` (114), `sftc_` (36), `sft_same_sign`, `sftb_` (6),
  `sft_mixed`, `sftd_` (188), `sft_loop`, `sft_signType_neg_ne_zero`, `sft_attachment_ne_zero`, `sft_signType_cases`,
  `thm_C_soft_of_cornerValues`, `thm_C_soft_of_floor`.
* **Rows**: `SM.cb_singleton`, `SM.corner_values`, `SM.thm_C_soft` (+ the reduced §7 `example` in CSoft).

## 2. Statement byte-identity (script `tools/port_stmt_check.py`, exit 0)

Namespace-aware scan of all 858 column-0 declarations of the assembled file and the 850 of the five port modules; for each
port declaration the STATEMENT (paragraph start — docstring / `omit … in` / `include … in` / `@[…]` — through the signature's
`:=`, or the whole paragraph for a `structure`) AND the whole paragraph (statement + body up to the next blank line) are compared
byte for byte with the same full name in the assembled file:
**846 identical (statement + block)**, **3 row theorems signature-identical** (`theorem cb_singleton : CbSingletonData :=`,
`theorem corner_values : CornerValuesData :=`, `theorem thm_C_soft : CSoftData :=` — the docstrings are new, §5, and the body
is the one-liner), **1 new `example`** (the reduced §7 check), **0 FAIL**.  No name declared twice in the port; coverage
of the assembled file exactly the expected nine absentees (3 deleted copies, 5 row-110 declarations, the frozen `example@12228`).
Independently, `tools/port_build.py` reports the omitted spans of §1 and nothing else.  Verdict: **every ported declaration's
statement is byte-identical to Wave2a_Assembled.lean; every body is verbatim except the three row one-liners.**

## 3. Excluded declarations (row 110 — NOT ported, stay in the draft)

| assembled lines | declaration | why |
|---|---|---|
| 5721-5732 | `s7_sliding_law_at` (docstring 5721-5723) | open leaf U110-E (`sorry`; wave 2b, needs `W2_S7A2` + `s7b_SlidingTransport.ret`) |
| 6881-6898 | `s7_bigon_law_at` | open leaf U110-K (`sorry`; wave 3, R-II deletion witness) |
| 7073-7098 | `thm_C_S7_of` | uses both open leaves (`sorryAx`) |
| 7100-7103 | `thm_C_S7_of_floor` | uses `thm_C_S7_of` |
| 12213-12216 | `thm_C_S7` (fixed name) | row 110 unmapped (D-F11/D-F14) |
| 12228-12229 | frozen `example` | its first conjunct is `thm_C_S7_of_floor hF`; reduced in `SM/CSoft.lean` to `⟨cb_singleton, corner_values, thm_C_soft⟩` |

**Dangling references: none.**  The compile of `CornerChainUnits.lean` is the proof (0 errors); a comment-aware grep of the
port modules for the five excluded names finds only headings ("fixed target name `SM.thm_C_S7`", assembled 1418 / 7107) and the
docstring mention of `s7_sliding_law_at` in the `s7c_` heading (assembled 4517).  The helper blocks `s7h_`, `s7i_`, `s7g_` that
sit between / after the excluded leaves in the frozen order do not use them.  Future row-110 port: a module `SM/CS7.lean`
importing `SM.CornerChainUnits` + `SM.CarrierFloorRows` receiving 5721-5732, 6881-6898, 7073-7103 (+ the `s7a2_` block and any
wave-2b/3 helpers) and `theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor` (statement line 12215).

## 4. Axioms (`#print axioms`, scratch `axioms_port.lean` importing the three row modules, 0 errors, 23 s)

| declaration | axioms |
|---|---|
| **`SM.cb_singleton`**, **`SM.corner_values`**, **`SM.thm_C_soft`** | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]` — exactly the expected nine, **no `sorryAx`** (= the axioms of `SM.thm_floor`) |
| `cb_singleton_of_floor`, `corner_values_of_floor`, `corner_values_of_singleton`, `thm_C_soft_of_cornerValues`, `thm_C_soft_of_floor`, `corner_values_i`, `sft_loop` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |
| `FloorTheoremData.slot_le_of_signed`, `CS7Data.bigon` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` |
| `s7_corner_product` | `[propext, Classical.choice, Quot.sound]` |

All registered in `work/lean/axiom-policy.json` (standard + literature).  Per-declaration union over the whole draft: WAVE2A §4.

## 5. Deviations from verbatim (each named in the module's header line)

1. **Statements**: `import SM.CarrierFloor` added after the 17 frozen imports (line 18); module docstring (assembled 19-43)
   reworded — the draft-state sentences ("Every `sorry` is either…", "Check: …", "§0 is a VERBATIM copy … to be deleted") replaced
   by a description of the module split and of the import; the "Sources / Dependencies / Fixed target names" paragraph and the
   `a_floor` / `z_parity` sentence kept verbatim; §0 heading (53-54) reworded; lines 60-92 deleted (§1); the four section
   closers `end Singleton` / `end CornerValues` / `end VertexEdge` / `end Soft` repeated after the bundles.
2. **Units**: import block = `import SM.CornerChainStatements` (the 17 frozen imports are carried transitively); new module
   docstring; the preamble (44-52), the §2-§5 headings/openers and closers repeated around the unit blocks.  No other text change:
   the 21 cosmetic warnings (8 × deprecated `if_neg`, 6 × unused auto-included section variable, 2 × deprecated `push_neg`, 5 ×
   unreferenced binder name `S`/`T`/`hS`; assembled lines 7308, 7446, 8046-8220, 8089, 8171, 8207, 10078, 10937, 10943, 10977,
   11018, 12033 — all pre-existing in the `sfta_`/`sftd_` blocks, WAVE2A §7 last paragraph) are left as they are (verbatim policy;
   none touches frozen text — the fixes the assembler lists change helper text only).
3. **Row modules** (pattern of `SM/CarrierFloorRows.lean`: plain `namespace SM … end SM`, no `open`, no classical attribute —
   confirmed unnecessary by the compile): import `SM.CornerChainUnits` + `SM.CarrierFloorRows`; the frozen docstrings
   ("Row 103 cb:singleton (proposed name).  Body once row 100 lands: `cb_singleton_of_floor thm_floor`." and the two like it,
   assembled 12204, 12208-12209, 12218-12219) replaced by docstrings describing the accepted state (row 100 HAS landed); the
   statement line kept byte-identical up to the ` by` of the draft's placeholder body, followed by the one-liner.  **`SM/CSoft.lean`
   additionally imports `SM.CBSingleton` and `SM.CornerValues`** for the reduced §7 example (its heading 12223-12227 verbatim).
4. **Redundancies with accepted lemmas** (WAVE2A §6: `sftb_markSuccessor_vertex_of_no_crossing`, `s7c_carrierWeight_eq_cornerSelector`,
   `sftc_regularPair_of_det_ne_zero`, `sftc_softOldIndex_pred/_succ_pred`, `sftc_softNewIndex_pred`, and the in-file duplicates
   `sftc_signType_cases` = `sft_signType_cases`, `sftc_sub_one_ne` = `sftb_sub_one_ne`) kept verbatim — different names, no clash.

## 6. Name-clash scan (script `tools/port_clash_scan.py`)

Namespace-aware full names of all **849** port declarations vs the **19,682** declarations of the **680** `.lean` files of
`work/lean` (SM, CV, RProof, Bridge, Supplemental; `.lake` excluded): **0 full-name clashes**, 0 duplicates inside the port.
The task's raw `grep -rnwE` over `work/lean/{SM,CV,RProof,Bridge}` for the **608** `SM.`-level short names (every frozen name
included — `cornerHomfly_ne_zero`, `SignedUniformOrOneDissent`, `CbSingletonData`, `cb_singleton`, …): **0 hits of any kind**
(the names are new to `work/lean`).  42 short-name coincidences inside prefixed namespaces (`s7b_ReturnTransport.*`,
`sfta_InsertMarkTransport.*`, `sftd_LoopTransport.*`, `sfta_IsInsertion.filter` vs `Carrier.MarkTransport.*`,
`GeoCarrier.GeoMarkTransport.*`, `Link.RecordIso.*`, `FrontRows.U2.*`, `Link.Diagram.visit_fst_eq_iff`,
`RProof.LocalTable.residual`, `Cycle.filter`) — distinct full names, informational, same list as WAVE2A §6; the compile under
the enlarged import closure confirms no ambiguity.  `FloorTheoremData.slot_le_of_signed` extends the accepted structure's
namespace (no clash: the accepted `SM/CarrierFloor.lean` declares no `slot_le_of_signed`).  Module names `SM.CornerChainStatements`,
`SM.CornerChainUnits`, `SM.CBSingleton`, `SM.CornerValues`, `SM.CSoft` do not exist under `work/lean/SM/`.

## 7. Compile recipe used (module semantics without touching `work/lean`)

Scratch tree `T/SM/` = copies of the five port files; `O/SM/` = symlinks to every file of `work/lean/.lake/build/lib/lean/SM/`
(3,175); from `work/lean`, in dependency order:
```
lake env lean ../drafts/corner/port/SM/CornerChainStatements.lean                     # plain form, 0 errors
lake env sh -c 'LEAN_PATH="O:$LEAN_PATH" lean --root=T -o O/SM/CornerChainStatements.olean T/SM/CornerChainStatements.lean'
…  CornerChainUnits, CBSingleton, CornerValues, CSoft likewise …
lake env sh -c 'LEAN_PATH="O:$LEAN_PATH" lean axioms_port.lean'                     # #print axioms (§4)
```
Every step exit 0 (log: scratchpad `compile_port.log`).  After the executor copies the files to `work/lean/SM/`, `lake build`
(glob `SM.+`) suffices.  Reproduce the port: `python3 tools/port_build.py [--time HH:MM]` (regenerates the five files from the
assembled file), `python3 tools/port_stmt_check.py`, `python3 tools/port_clash_scan.py`.

## 8. The three row theorem statements (exact)

```lean
theorem cb_singleton : CbSingletonData := cb_singleton_of_floor thm_floor          -- SM/CBSingleton.lean:12
theorem corner_values : CornerValuesData := corner_values_of_floor thm_floor       -- SM/CornerValues.lean:12
theorem thm_C_soft : CSoftData := thm_C_soft_of_floor thm_floor                    -- SM/CSoft.lean:14
```
(`SM.thm_floor : FloorTheoremData` = `work/lean/SM/CarrierFloorRows.lean:13`.)  Consumer check in `SM/CSoft.lean`:
`example : CbSingletonData ∧ CornerValuesData ∧ CSoftData := ⟨cb_singleton, corner_values, thm_C_soft⟩`.

## 9. For the executor to decide

1. Header time placeholder `<HH:MM>Z` in line 1 of each module (`tools/port_build.py --time HH:MM` fills it).
2. Row-theorem docstrings are new (§5.3); revert to the frozen ones (quoted there) if the checker wants docstring identity.
3. Drop the §7 `example` and the two extra imports of `SM/CSoft.lean` if a row module should import nothing beyond Units + Rows.
4. Single `CornerChainUnits.lean` (11,842 lines, 33 s).  If a split is wanted: `CornerChainUnits1` = §2+§3 (port lines 1-1217),
   `CornerChainUnits2` = §4 (1218-6935), `CornerChainUnits3` = §5 (6936-11842, imports 1 for `sge_`) — pure cut at the
   `/-! ## §…` headings, no text change.
5. `lean-declarations.json`: `cb:singleton` → `SM.cb_singleton` / `SM.CBSingleton`; `lem:corner-values` → `SM.corner_values` /
   `SM.CornerValues`; `thm:C-soft` → `SM.thm_C_soft` / `SM.CSoft`; `thm:C-S7` stays pending (statement `SM.CS7Data` is in
   `SM.CornerChainStatements`).
6. The 21 cosmetic warnings (§5.2) — leave, or apply the assembler's fixes at port (helper text only).
