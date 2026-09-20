# PORT_REPORT — comparison lane: port of rows 122 prop:anchor-values, 127 thm:comparison, 128 cor:C-inherits (2026-09-15 20:25 UTC / 4:25pm ET)

Porter subagent.  Source: `work/drafts/comparison/Comparison_Assembled.lean` (1052 lines, sha256
`af45ce05ea4124702604d91e8e4cfde8c2174029573cfeb779bf6439774ef21a`); plan: `ASSEMBLY_REPORT.md` §7 and `PLAN_FINAL.md` §4
(U-CM-ROWS), §6.  Nothing was written under `work/lean`; `lake build` was not run; every compile used the scratch `.olean`
recipe of `work/drafts/cvtail/port/PORT_REPORT.md` §8.5 (`tools/port_compile.sh`, §4 below).  Output, all under
`work/drafts/comparison/port/`:

| module | lines | sha256 (prefix) | assembled source lines (verbatim) | compile (`lean --root -o`, scratch tree) |
|---|---|---|---|---|
| `SM/CornerPolygon.lean` (§1, library) | 74 | `9ad7f811…984d6` | 131-186 | 0 errors, 1 warning (frozen `hn`, §4), 20 s |
| `SM/AnchorValues.lean` (§2, row 122 library) | 271 | `e71e22f6…19972` | 188-439 | 0 errors, 2 warnings (frozen `hn`), 35 s |
| `SM/AnchorValuesRow.lean` (row 122 theorem) | 14 | `db9f5d05…828ef` | signature line 1004 (docstring 1003 rewritten) | 0 errors, 0 warnings, 33 s |
| `SM/CuspDeletionGeneric.lean` (unit U-CM-CUSPGEN) | 186 | `a2964a22…df9248` | 772-936 | 0 errors, 0 warnings, 15 s |
| `SM/Comparison.lean` (§3, row 127 library) | 260 | `1ff9c235…8a95d5` | 441-677 | 0 errors, 0 warnings, 30 s |
| `SM/CInherits.lean` (§4 + §6, row 128 library) | 204 | `bff23f79…424cfb` | 679-768, 938-997, 1019-1050 | 0 errors, 0 warnings, 30 s |

`grep -c sorry` = 0 in every module (also 0 `#print`, `#eval`, `#check`, `admit`, `set_option`, `import SM.CS5`).  Header line 1 of
every module follows the executor's template with the placeholder `<HH:MM>Z`.  Row-122 module choice: a SEPARATE row module
`SM/AnchorValuesRow.lean` (the corner lane's pattern SM/CSoft.lean / SM/CornerValues.lean: the library module stays independent
of the row-112 module; `SM.CSoft` imports `SM.CornerChainUnits`, 11.8k lines).  The rows 127/128 theorems are NOT declared
(they need `SM.thm_C_S7`); their one-liners are in §5.

## 1. The four DELETED §0 copies — byte-identical to the accepted declarations (task 1)

`tools/port_copy_diff.py` (declaration line through the end of its paragraph = statement + fields / proof; exit 0):

| copy (assembled) | accepted declaration | declaration block | docstring |
|---|---|---|---|
| `CS7Data` (60-69) | `work/lean/SM/CornerChainStatements.lean:232` | **IDENTICAL** (10 lines) | differs (the copy's is the lane's annotation) |
| `CSoftData` (72-77) | `work/lean/SM/CornerChainStatements.lean:289` | **IDENTICAL** (6 lines) | differs (same) |
| `cvl_embedded_of_no_crossings` (82-101) | `work/lean/SM/CornerChainUnits.lean:1158` | **IDENTICAL** (20 lines) | differs (same) |
| `corner_values_i` (106-127) | `work/lean/SM/CornerChainUnits.lean:1184` | **IDENTICAL** (22 lines) | differs (same) |

Both sides declare the same wrapper `variable {n : ℕ} [NeZero n]`; the accepted modules additionally run under
`attribute [local instance] Classical.propDecidable` / `noncomputable section`, which does not enter the (instance-free)
statements the consumers read (`corner_values_i … .2.2`, `h7.vertex_edge_law`, `hs.soft_theorem`) — confirmed by the
compile of `SM/Comparison.lean` / `SM/CInherits.lean` against the accepted declarations.  So §0 (assembled 51-129, including its
`section CornerInterfaces` / `open Link`) is deleted and replaced by `import SM.CornerChainStatements` (in
`SM/AnchorValues.lean`; carried transitively to the rest) and `import SM.CornerChainUnits` (in `SM/Comparison.lean`).  No item
stopped.

## 2. Module contents (assembled ranges, imports, what resolves where)

Wrappers repeated in every module: `namespace SM` (assembled 47) … `end SM` (1052); the file-level `open WallGerm SoftDuplication
Carrier` (49) verbatim in `AnchorValues`, `Comparison`, `CInherits`, REDUCED to `open WallGerm Carrier` in `CornerPolygon` and to
`open WallGerm` in `CuspDeletionGeneric` (Lean 4 rejects `open` of a namespace absent from the import closure; `SoftDuplication`
is not in the CChamber closure, neither `SoftDuplication` nor `Carrier` in the cusp-deletion closure; nothing in those sections
uses the dropped namespaces — compile-verified).  The assembled file uses NO `attribute [local instance]`, `set_option` or
`noncomputable section`, so nothing else had to be repeated (`cornerPolygonSum`, `cornerPolygon` carry their own `noncomputable`).

| module | imports (compile-verified sufficient) | declarations (full names `SM.…`) |
|---|---|---|
| `CornerPolygon` | `SM.CChamber` (alone replaces the draft's 14 imports; brings Chambers / CyclicChambers / CornerStateSum) | `cp_cornerStateSum_compat`, `cornerPolygonSum`, `cornerPolygonSum_projection`, `cp_cornerStateSum_congr`, `cornerPolygon`, `cornerPolygon_projection`, `cornerPolygon_projection'`, `cornerPolygon_chamber` (8) |
| `AnchorValues` | `SM.CornerPolygon`, `SM.Uniqueness`, `SM.CornerChainStatements` (`CSoftData`) | `AnchorValuesHypotheses`, `UniquenessHypotheses.toAnchorValuesHypotheses`, `AnchorValuesData`, `av_softAnchor_value`, `av_zero`, `av_loop`, `av_treeCoefficient_anchor`, `av_A_zero`, `av_A_loop`, `av_loopZero_turn`, `cornerPolygon_soft_of`, `cornerPolygon_anchorValuesHypotheses_of`, `anchor_values_of`, `AnchorValuesData.C_zero`, `.C_loop`, `.C_loopZero` (16) |
| `AnchorValuesRow` | `SM.AnchorValues`, `SM.CSoft` | `prop_anchor_values` (1) |
| `CuspDeletionGeneric` | `SM.CuspDefinition`, `SM.DeletionIndices`, `SM.DeletedTuple`, `SM.GenericTopology`, `SM.ZeroTriples` | `cu_fused_interior_true`, `cu_fused_interior_false`, `cu_deletionIndex_adjacent`, `cu_deletionIndex_remote`, `cu_deletionIndex_two_prev`, `cu_remote_prev`, `cu_remote_deleted`, `cu_lift`, `cu_lift_remote`, `cu_lift_interior`, `cusp_deletion_generic` (11) |
| `Comparison` | `SM.AnchorValues`, `SM.CornerChainUnits` (`corner_values_i`), `SM.CS3`, `SM.CSilent`, `SM.HypR` | `TrianglesC`, `tri_cornerStateSum_crossingFree`, `tri_triangle_no_crossing`, `tri_leftTurns_star_one`, `tri_leftTurns_starNeg_one`, `tri_triangle_value`, `trianglesC`, `cs3_param_side`, `cs3_flat_bridge`, `cs3_flat_law_C`, `uniquenessHypotheses_C_of`, `thm_comparison_of`, `thm_comparison_root_of`, `thm_comparison_polygon_of` (14) |
| `CInherits` | `SM.Comparison`, `SM.CuspDeletionGeneric` | `CuspLawC`, `ReversalLawC`, `CInheritsData`, `cu_cuspLawC_of`, `cor_C_inherits_of` + the six §6 `example`s (11) |

Range boundaries are guarded by text assertions in `tools/port_build.py` (re-runnable; `--time HH:MM` fills the header).
Not ported: §0 (51-129, deleted), the §5 block 999-1017 except the row-122 signature (the deferred rows 127/128, §5 below), the
stale section comment 770 (`### The cusp law — the ONE open leaf of the lane …`, dropped: the leaf is proved), the module
docstring 16-45 (rewritten per module, provenance kept: source lines, fixed names, policy mode, FR-CM references, the
D-F11/D-F14 sentence).

## 3. Statement / block identity with Comparison_Assembled.lean (task 4)

`tools/port_stmt_check.py` (namespace-aware; statement = paragraph start through the depth-relevant `:=` / ` where`, whole
paragraph for structures; block = whole paragraph; `example`s matched by whole block; exit 0):

| result | count |
|---|---|
| declarations identical, statement AND block | **54 / 54** |
| row theorem `SM.prop_anchor_values`: signature identical to line 1004, docstring new, body `anchor_values_of thm_C_soft` | 1 |
| `example` blocks verbatim (the six §6 checks) | **6 / 6** |
| FAIL | 0 |
| assembled declarations absent from the port | exactly the expected 6: the four deleted §0 copies + `SM.thm_comparison`, `SM.cor_C_inherits` (deferred) |
| declared twice in the port / in the assembled file | none / none |

Complete deviation list (`tools/port_deviation.py`: every non-blank port line absent from the assembled file — 61 lines in all):
the 6 header lines; the import lines (`SM.CornerPolygon`, `SM.CornerChainStatements`, `SM.AnchorValues`, `SM.CSoft`,
`SM.CornerChainUnits`, `SM.Comparison`, `SM.CuspDeletionGeneric`, `SM.CuspDefinition`, `SM.DeletionIndices`, `SM.DeletedTuple`,
`SM.GenericTopology`, `SM.ZeroTriples`; `SM.Uniqueness`, `SM.CS3`, `SM.CSilent`, `SM.HypR`, `SM.CChamber` coincide with draft
lines); the 6 module docstrings (36 lines); the two reduced `open` lines; the row-122 docstring (3 lines) and its one-line
theorem.  No other line of any module is new; in particular no statement, proof, field, docstring of a declaration, section
heading (other than the dropped 770) or `open` inside a section changed.

## 4. Compile and axioms (task 4)

Recipe (`tools/port_compile.sh <scratchdir>`; true module semantics without touching `work/lean`): copy the modules into a
scratch tree `T/SM/`, symlink every `work/lean/.lake/build/lib/lean/SM/*.olean` (and `.ilean`) into `O/SM/`, then from
`work/lean`: `lake env sh -c 'LEAN_PATH="O:$LEAN_PATH" lean --root=T -o O/SM/X.olean -i O/SM/X.ilean T/SM/X.lean'` in the order
CornerPolygon, CuspDeletionGeneric, AnchorValues, AnchorValuesRow, Comparison, CInherits (sequential — the machine is loaded);
finally the scratch importer `T/Axioms.lean` (`import SM.AnchorValuesRow`, `import SM.CInherits`, fourteen `#print axioms`).
All six: exit 0, **0 errors**.  Warnings: exactly the 3 pre-existing `unusedVariables` notes on the FROZEN `hn` binders —
`CornerPolygon.lean:65:54` (`cornerPolygon_chamber`, assembled 179), `AnchorValues.lean:27:34` and `:30:31`
(`AnchorValuesHypotheses.chamber` / `.soft`, assembled 197, 200); the binders are left verbatim as instructed (they mirror
`UniquenessHypotheses`, SM/Uniqueness.lean:37-38, 72-76, which silences the same linter with
`set_option linter.unusedVariables false` at line 3 — the executor may add that line after the imports; zero statement change).

`#print axioms` (scratch importer, verbatim; log `…/scratchpad/logs/axioms.log`; **no `sorryAx` anywhere**):

| declaration | axioms |
|---|---|
| **`SM.prop_anchor_values`** (row 122) | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact` — exactly the nine registered axioms (= those of `SM.thm_C_soft`, also probed) |
| `SM.anchor_values_of`, `SM.cu_cuspLawC_of`, `SM.cornerPolygon`, `SM.cornerPolygon_chamber`, `SM.cs3_flat_law_C` | standard + `SM.lit_homfly` |
| `SM.thm_comparison_of`, `SM.cor_C_inherits_of`, `SM.trianglesC`, `SM.uniquenessHypotheses_C_of`, `SM.thm_comparison_root_of`, `SM.thm_comparison_polygon_of` | standard + `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` |
| `SM.cusp_deletion_generic` (the leaf) | `propext, Classical.choice, Quot.sound` only |

Identical to ASSEMBLY_REPORT.md §4 for every `_of` theorem, companion and the leaf (the port changed no proof term).

## 5. The row theorems (task 2, task 3)

Row 122, PORTED (`SM/AnchorValuesRow.lean`; signature = assembled line 1004 minus the placeholder's trailing ` by`; body = the
composition PLAN_FINAL.md §4 (U-CM-ROWS) / §5 and the frozen docstring 1003 prescribe — `anchor_values_of` applied to the
accepted `SM.thm_C_soft : CSoftData`, SM/CSoft.lean):

```lean
theorem prop_anchor_values : AnchorValuesData := anchor_values_of thm_C_soft
```

Rows 127 / 128, NOT declared (FIXED names; both bodies need `SM.thm_C_S7 : CS7Data`, row 110, which does not exist yet — its
statement `CS7Data` does).  The two one-liners the executor adds the moment `SM.thm_C_S7` lands (signatures verbatim from
assembled 1009-1011 and 1016; bodies from PLAN_FINAL.md §4/§5 and the frozen docstrings 1007-1008, 1014-1015):

```lean
/-- Row 127 thm:comparison (FIXED name; hyp:R explicit).  "Assume Hypothesis R.  Then C(P) = A(P) for
every generic polygon P." -/
theorem thm_comparison (hR : hyp_R) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn :=
  thm_comparison_of hR thm_C_S7 thm_C_soft

/-- Row 128 cor:C-inherits (FIXED name; hyp:R explicit). -/
theorem cor_C_inherits (hR : hyp_R) : CInheritsData := cor_C_inherits_of hR thm_C_S7 thm_C_soft
```

Placement (executor's call): a small row module `SM/ComparisonRows.lean` importing `SM.CInherits`, `SM.CSoft` and the row-110
module (the pattern of SM/CSoft.lean and of `SM/AnchorValuesRow.lean` here, keeping the library modules independent of row 110),
or appended to `SM/Comparison.lean` / `SM/CInherits.lean` as ASSEMBLY_REPORT §7 sketched (then those two modules must import the
row-110 module).  The §6 `example`s already in `SM/CInherits.lean` are the consumer shape checks; the CV/R tail's
`corner_laws_and_soft` final line reads `cor_C_inherits Bridge.sm_R` (§8).

## 6. Clash scan (task 4)

`tools/port_clash_scan.py` (namespace-aware, all 685 project `.lean` files under `work/lean` incl. the new corner modules,
`.lake` excluded — 20,531 library declarations; plus the task's raw `grep -rnwE` of the 40 SM-level short names over
`work/lean/{SM,CV,RProof,Bridge}`): **0 full-name clashes, 0 short-name coincidences in any namespace, 0 raw word hits** for all
44 named port declarations.  (`TrianglesC`, `CuspLawC`, `ReversalLawC`, `CInheritsData` exist only in the drafts — cvtail
Wave1 — not in `work/lean`; the tail must NOT port its copies, §8.)

## 7. Notes for the executor (decisions)

1. **`lake build` picks the modules up automatically**: `work/lean/lakefile.toml` globs `SM.+`; copy the six files to
   `work/lean/SM/` and build in the order of §4 (or just `lake build`).  Header time placeholder `<HH:MM>Z` in line 1 of each.
2. **Linter**: leave the 3 `hn` notes, or add `set_option linter.unusedVariables false` after the imports of
   `SM/CornerPolygon.lean` and `SM/AnchorValues.lean` (SM/Uniqueness.lean:3 precedent) — no statement change either way.
3. **`lean-declarations.json`**: `prop:anchor-values` → `declaration: "SM.prop_anchor_values"`, `module: "SM.AnchorValuesRow"`,
   `status: implemented` (as the corner lane recorded `thm:C-soft` → `SM.CSoft`); `statement_sha256` is computed by
   `tools/check_lean.py` at mapping time.  `thm:comparison` / `cor:C-inherits` stay `pending` (fixed names already recorded)
   until §5's one-liners exist.
4. **AUTHOR_NOTES disclosures before mapping** (ASSEMBLY_REPORT §7.4; not yet in the FR-CM list): FR-CM-3′ (`AnchorValuesData`'s
   zero/loop/A_* clauses quantify over every anchor datum without def:anchors' case conditions — a proved generalisation),
   FR-CM-9′ (`CuspLawC`'s `G1 (deleteVertex …)` premise is implied by `w.CuspAt j`; kept for fidelity), and the keep/drop of
   `CInheritsData.root_values` (FR-CM-13; the port keeps it, as frozen).
5. The `open` reductions in `CornerPolygon` / `CuspDeletionGeneric` (§2) are forced by Lean, not stylistic; if the executor prefers
   the verbatim `open` line, add `import SM.SoftInsertionTuple` (namespace `SoftDuplication`) resp. `import SM.CChamber` +
   `SM.SoftInsertionTuple` — heavier imports for no semantic gain; not recommended.
6. Rows 127/128 remain "conditional-complete on rows 110/112" (PLAN_FINAL §4) — with row 112 landed, only row 110 is open.

## 8. The CV/R tail's row-184 draft (work/drafts/cvtail/Wave1_Assembled.lean §5, lines 4265-4386) — exact edits to consume THIS lane's port

`tools/port_tail_diff.py` (declaration blocks, byte-for-byte):

| Wave1 declaration | vs this lane's port | verdict / edit |
|---|---|---|
| `def CuspLawC` (4268) | `SM/CInherits.lean:24` | declaration block **IDENTICAL** (docstring differs) → DELETE the tail's copy (4265-4280) and `import SM.CInherits` |
| `def ReversalLawC` (4282) | `SM/CInherits.lean:39` | **IDENTICAL** → DELETE (4281-4284) |
| `def CyclicLawC` (4287) | — | not this lane's; stays the tail's own (PLAN_FINAL §6.3) |
| `def TrianglesC` (4292) | `SM/Comparison.lean:26` | **IDENTICAL** → DELETE (4291-4295); `SM.Comparison` comes with `import SM.CInherits` |
| `structure CInheritsData` (4301, 11 fields) | `SM/CInherits.lean:52` (12 fields) | **DIFFERS**, as PLAN_FINAL §6.1 prescribes → DELETE the tail's block (4296-4329): this lane's adds `root_values` (first field), retypes `vertex_edge_law : CS7Data` → the `Generic λ₁ ∧ Generic λ₂ ∧ ∀ s t …` field, `triple_law : hyp_R` → `∀ n hn w e f k, TripleAt → ∀ s t, …`, `soft_theorem : CSoftData` → `∃ ε₁ > 0, ∀ ε < ε₁, ∃ hQ, …`, and carries field docstrings |
| `theorem cor_C_inherits (_hR : hyp_R) : CInheritsData := by sorry` (4331) | deferred (§5) | keep the placeholder until `SM.cor_C_inherits` exists, then DELETE (PLAN_FINAL §6.2); note its binder is `_hR` while the FIXED signature is `(hR : hyp_R)` |
| `structure CornerLawsAndSoftData` (4337), `theorem corner_laws_and_soft_of` (4367) | reads `hinh.cusp_law`, `hinh.reversal_law`, `hinh.triangles` only | **NO change** — the three fields keep their types (`CInherits.lean` §6 first `example` certifies `CInheritsData → CuspLawC ∧ ReversalLawC ∧ TrianglesC`) |
| `theorem corner_laws_and_soft` (4383) | `corner_laws_and_soft_of Bridge.sm_R thm_C_S7 thm_C_soft (cor_C_inherits Bridge.sm_R)` | unchanged text; waits for `Bridge.sm_R`, `SM.thm_C_S7`, `SM.cor_C_inherits` |

So the tail ports NONE of the three Props nor the bundle: after this lane's modules land, its §5 module needs `import SM.CInherits`
(+ the corner rows module for `CS7Data` / `CSoftData`, already accepted: `SM.CornerChainStatements`), keeps `CyclicLawC`,
`CornerLawsAndSoftData`, `corner_laws_and_soft_of` verbatim, and adds `corner_laws_and_soft` when its three inputs exist.

## 9. Files

- `work/drafts/comparison/port/SM/{CornerPolygon,AnchorValues,AnchorValuesRow,CuspDeletionGeneric,Comparison,CInherits}.lean` — the port-ready modules.
- `work/drafts/comparison/port/tools/port_build.py` (builder, guarded ranges), `port_stmt_check.py` (statement / block identity),
  `port_copy_diff.py` (§0 copies vs work/lean), `port_clash_scan.py`, `port_deviation.py` (complete deviation list),
  `port_tail_diff.py` (cvtail Wave1 §5 vs port), `port_compile.sh` (scratch `.olean` recipe + axiom probe).
- Scratchpad only (not part of the lane): `porttree/{T,O}`, `logs/*.log` (per-module compile logs, `axioms.log`), `manifest.json`,
  `stmt.json`, `clash.json`, `deviations.txt`.
