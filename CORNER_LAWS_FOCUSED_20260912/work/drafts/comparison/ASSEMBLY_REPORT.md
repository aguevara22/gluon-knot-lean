# ASSEMBLY_REPORT — comparison lane: rows 122 prop:anchor-values, 127 thm:comparison, 128 cor:C-inherits

Written 2026-09-15 17:59 UTC / 1:59pm ET by the assembler subagent.
File: `work/drafts/comparison/Comparison_Assembled.lean` (1052 lines, 61 declarations), produced by
`work/drafts/comparison/assemble_comparison.py` from `Statements_FINAL.lean` (896 lines, the frozen skeleton)
and the ONE unit file `U_CUSPGEN.lean` (unit U-CM-CUSPGEN, leaf `cusp_deletion_generic`).
Check: `cd work/lean && lake env lean ../drafts/comparison/Comparison_Assembled.lean` → exit 0, **0 errors**,
21.7 s wall (Mathlib olean load dominates).  Nothing was written under `work/lean`; `lake build` was not run.

## Headline

| check | result |
|---|---|
| leaves proved | **1 / 1** (`cusp_deletion_generic`, sm-6:335-359, frozen statement, domain NOT narrowed); unproved leaves: **none** |
| `grep -c sorry` | **5** = the 3 §5 placeholder bodies (lines 1005, 1012, 1017: `prop_anchor_values`, `thm_comparison`, `cor_C_inherits`, which wait for rows 110/112 by design, D-F11/D-F14) + 2 prose mentions (line 25 module docstring, line 999 §5 section header) |
| compile | exit 0, 0 errors, 6 warnings: 3 pre-existing `unusedVariables` notes on the `hn` binders of the FROZEN statements (lines 179 `cornerPolygon_chamber`, 197 `AnchorValuesHypotheses.chamber`, 200 `.soft`) + 3 `declaration uses sorry` (lines 1004, 1009, 1016 = the §5 placeholders) |
| `#print axioms` (scratchpad copy) | `anchor_values_of` = standard + `SM.lit_homfly`; `thm_comparison_of`, `cor_C_inherits_of`, `trianglesC` = standard + `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness`; `cusp_deletion_generic` = standard only; **no `sorryAx` in any `_of` theorem, companion, or the leaf** — `sorryAx` appears ONLY in the three §5 placeholders (see §4) |
| Statements_FINAL.lean byte identity | all **51 / 51** declaration statements (declaration line through its depth-0 `:=` / `where`; whole block for the 4 structures) and all **71 / 71** docstring blocks are contiguous, byte-identical, unique substrings of the assembled file; `diff Statements_FINAL.lean Comparison_Assembled.lean` = 3 module-docstring hunks + the 2 unit hunks, nothing else |
| name clashes against work/lean | **none** (namespace-aware scan of all 61 declarations over the 676 project `.lean` files: 0 exact full-name hits, 0 short-name hits in any namespace; no in-file duplicates) |
| `#print` / `#eval` / `#check` lines | none in the file (the unit had none; the axiom probe lives in the scratchpad only) |
| module docstring | title, check line and the "every `sorry`" state paragraph rewritten by exact-match replacement (script aborts if the header drifted); nothing else in the header changed |

## 1. Unit-diff audit (task 1) — ADOPTED, no violation

`diff Statements_FINAL.lean U_CUSPGEN.lean` has exactly two hunks, both re-derived by the script (difflib, autojunk off):

| hunk (skeleton coords) | content | verdict |
|---|---|---|
| `769a770,905` | pure insertion of 136 lines immediately before the leaf's docstring: a `/-! #### Helpers of unit U-CM-CUSPGEN … -/` section comment + 10 declarations, all `cu_`-prefixed, none redeclaring a skeleton name | helpers, allowed |
| `780c916,934` | the single line `  sorry` (the body of `cusp_deletion_generic`) → a 19-line tactic proof; the `theorem … := by` statement line (skeleton 778-779) untouched | the leaf's body, allowed |

Script guards that all passed: every removed skeleton line is a `sorry`; its owning declaration is the unit's own leaf
(`cusp_deletion_generic`) and not one of the §5 placeholders; every added declaration carries the prefix `cu_` and is
not a skeleton name; the three §5 placeholders keep their `sorry` (unit lines 1003 / 1010 / 1015 = assembled
1005 / 1012 / 1017); no statement, definition, structure, name, import, `open`, `section`, or docstring changed.
The unit report's claims (0 errors, 16.6 s; 6 → 5 sorries; two hunks; standard axioms for the leaf) were all
re-verified here: the unit file recompiled with the official command at exit 0, 0 errors, 6 warnings, 19.4 s.

Helpers adopted (assembled-file lines; all with explicit `{n : ℕ} [NeZero n]` binders, `[Nontrivial (ZMod n)]` where `−2 ≠ −1` is used):

| line | declaration | role (PLAN_FINAL.md §3.4 step) |
|---|---|---|
| 779 | `theorem cu_fused_interior_true` | step 2: `StrictBetween A B M` ⇒ relint of the fused edge `[A,B]` of `Q` ⊂ relint `E_{j−1}(P) = [A,M]` (parameter `q·t`) |
| 792 | `theorem cu_fused_interior_false` | step 2: `StrictBetween M A B` ⇒ relint `[A,B]` ⊂ relint `E_j(P) = [M,B]` (parameter `t + q(1−t)`) |
| 805 | `theorem cu_deletionIndex_adjacent` | step 4: `adjacent (dI a) (dI b) → adjacent a b` for retained `a, b ≠ −1` |
| 826 | `theorem cu_deletionIndex_remote` | step 4: contrapositive — remoteness of retained edges transfers `Q → P` |
| 832 | `theorem cu_deletionIndex_two_prev` | step 4: `deletionIndex j (−2) = j − 2` |
| 841 | `theorem cu_remote_prev` | step 4: retained edge remote from the fused edge in `Q` is remote from `j−1` in `P` |
| 856 | `theorem cu_remote_deleted` | step 4: … remote from `j` in `P` |
| 871 | `def cu_lift` | step 3: the edge lift `ZMod n → ZMod (n+1)`, `−1 ↦ k ∈ {j−1, j}`, else `deletionIndex j` |
| 875 | `theorem cu_lift_remote` | step 4: the lift carries remote pairs to remote pairs (hence injective on them) |
| 898 | `theorem cu_lift_interior` | step 3: relint points lift into the relint of the lifted edge (`edgeInterior_deleteVertex` / `hfused`) |
| 916 | `theorem cusp_deletion_generic` (LEAF, statement frozen) | step 5: `⟨hQ1, _⟩`; `3 ≤ n` from `hf.1`; `cusp_cases` → `k`; `g1_common_interiors_remote` × 3; `mem_concurrenceTriples` + `concurrenceTriple_iff` on the lifted triple; contradiction with `hf.2.2.1 : concurrences = ∅` |

## 2. Assembly (task 2)

`assemble_comparison.py`: hunks applied in one pass in skeleton order (pairwise-disjoint check), each inserted block
verified to occur contiguously in the output, every non-`sorry` skeleton line verified to survive in order, every
skeleton declaration statement and docstring verified byte-identical (§5 below).  De-duplication: one unit only —
no duplicate helpers to drop or rename (the script would drop identical duplicates and abort on differing same-name
helpers); the in-file scan shows no duplicate full names among the 61 declarations.  `#print`/`#eval`/`#check`
removal: nothing to remove.

Layout of `Comparison_Assembled.lean` (line ranges):

| lines | content |
|---|---|
| 1-14 | imports (verbatim; `import SM.CS5` is unused — see port plan 7.5) |
| 16-45 | module docstring (title / check line / state paragraph rewritten; rest verbatim) |
| 47-49 | `namespace SM`, `open WallGerm SoftDuplication Carrier` |
| 51-129 | §0 `section CornerInterfaces` — VERBATIM corner-lane copies: `CS7Data` (60), `CSoftData` (72), `cvl_embedded_of_no_crossings` (82), `corner_values_i` (106) — TO BE UNIFIED |
| 131-186 | §1 descent `cp_*`, `cornerPolygonSum`, `cornerPolygon`, projections, `cornerPolygon_chamber` |
| 188-439 | §2 row 122: `AnchorValuesHypotheses` (195), `AnchorValuesData` (220), `av_*`, `cornerPolygon_soft_of`, `anchor_values_of` (404), companions |
| 441-677 | §3 row 127: `TrianglesC` (445, CV/R-tail copy), `tri_*`, `trianglesC` (538), `cs3_*`, `uniquenessHypotheses_C_of` (616), `thm_comparison_of` (652), companions (662, 670) |
| 679-997 | §4 row 128: `CuspLawC` (684), `ReversalLawC` (699) (CV/R-tail copies), `CInheritsData` (712), **helpers `cu_*` (772-907, inserted)**, `cusp_deletion_generic` (916, **proved**), `cu_cuspLawC_of` (940), `cor_C_inherits_of` (963) |
| 999-1017 | §5 the three row theorems (placeholders, `sorry` by design until rows 110/112) |
| 1019-1052 | §6 consumer / equivalence `example`s (all proved), `end SM` |

## 3. Unproved leaves (task 3)

None.  The lane's ONE leaf is proved as frozen (no hypothesis added, threaded cusps included, `n = 3` covered by
`3 ≤ n` from `hf.1 : 4 ≤ n + 1`).  The only `sorry` bodies are the three §5 row theorems, which are not leaves: their
bodies are fixed by PLAN_FINAL.md §5 as `anchor_values_of thm_C_soft`, `thm_comparison_of hR thm_C_S7 thm_C_soft`,
`cor_C_inherits_of hR thm_C_S7 thm_C_soft` and can only be written once `SM.thm_C_S7 : CS7Data` (row 110) and
`SM.thm_C_soft : CSoftData` (row 112) exist in the library (both `pending` in `work/lean/lean-declarations.json`).
No assembler proving time was needed.

## 4. Compile and axioms (task 4)

Official compile (`cd work/lean && lake env lean ../drafts/comparison/Comparison_Assembled.lean`): exit 0, 0 errors,
6 warnings (listed in the headline; the 3 `hn` notes are in frozen statements, the 3 `sorry` notes are the §5
placeholders).  Axiom probe on the scratchpad copy `…/scratchpad/Comparison_axprobe.lean` (the assembled file +
15 `#print axioms` lines appended; compiled with the same command), verbatim results:

| declaration | axioms |
|---|---|
| `SM.anchor_values_of` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` |
| `SM.thm_comparison_of` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |
| `SM.cor_C_inherits_of` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |
| `SM.trianglesC` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |
| `SM.cusp_deletion_generic` (the leaf) | `[propext, Classical.choice, Quot.sound]` |
| `SM.cu_cuspLawC_of` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` |
| `SM.uniquenessHypotheses_C_of`, `SM.thm_comparison_root_of`, `SM.thm_comparison_polygon_of`, `SM.corner_values_i` | standard + `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` |
| `SM.cornerPolygon`, `SM.cs3_flat_law_C` | standard + `SM.lit_homfly` |
| `SM.prop_anchor_values`, `SM.thm_comparison`, `SM.cor_C_inherits` (§5 placeholders) | standard + `sorryAx` + `SM.lit_homfly` — expected; they become sorry-free one-liners with rows 110/112 |

All non-standard axioms are registered literature axioms of `work/lean/axiom-policy.json` (`lit:homfly`, `lp:lm`,
`lp:lm-uniqueness`), entering through def:C (`cornerStateSum` → `cornerCoefficient` → `homfly`) and thm:uniqueness /
cor:A-lawful, exactly as PLAN_FINAL.md §4 predicted.  `SM.lit_homfly_descent` and `SM.src_contact` do not appear (they
enter only when the corner rows are plugged in).  `SM.hyp_R` is a definition taken as the explicit parameter `hR`, never
an axiom.  Before assembly `cor_C_inherits_of` carried `sorryAx` through the leaf; it no longer does.

## 5. Byte identity with Statements_FINAL.lean (task 5)

Method (in the script): for each of the 51 skeleton declarations (`theorem`/`def`/`structure`; the 6 `example`s have no
name and are covered by the line-survival check), the statement text = declaration line through the first `:=` or
` where` at bracket depth 0 (so `(by have := hf.1; omega)` binders stay inside the statement), or the whole block for a
`structure`; each must occur exactly once in the assembled file — **51/51 pass**.  Each of the 71 `/-- … -/` docstring
blocks occurs verbatim — **71/71 pass**.  Every non-`sorry` skeleton line survives in order.  Independent cross-check:
`diff Statements_FINAL.lean Comparison_Assembled.lean` hunks are `16,17c16,18`, `20c21`, `22,25c23,27` (module
docstring only), `769a772,907` (helpers), `780c918,936` (leaf body) — no other line differs.  In particular the fixed-name
rows `thm_comparison (hR : hyp_R) : ∀ n [NeZero n] (hn) (P) (hP), cornerStateSum hn hP = amplitude P hP.1 hn` and
`cor_C_inherits (hR : hyp_R) : CInheritsData`, the proposed `prop_anchor_values : AnchorValuesData`, and the §0/§3/§4
copies are byte-identical to the skeleton.  The seven copied interface blocks were also re-checked against THEIR
sources: `CS7Data`, `CSoftData`, `cvl_embedded_of_no_crossings`, `corner_values_i` = corner/Statements_FINAL.lean
:412-421, :557-562, :324-343, :350-371; `CuspLawC`, `ReversalLawC`, `TrianglesC` = cvtail/Statements_FINAL.lean :874-885,
:888-890, :898-900 — all byte-identical.

## 6. Name-clash scan (task 6)

Namespace-aware scan (`scratchpad/clash_scan.py`): every declaration of the assembled file is resolved to its full
name (`SM.…`, tracking `namespace`/`end`), then every project `.lean` file under `work/lean` (676 files, `.lake`
excluded) is searched for a declaration of the same short name and its namespace is resolved the same way.
Result: **0 exact full-name clashes, 0 short-name hits in any namespace** for all 61 declarations — in particular for
the 10 new `cu_*` helpers and the pre-existing `cu_cuspLawC_of` (the `cu_` prefix is unused anywhere in work/lean).
Sanity of the scan: it finds `theorem uniqueness` at SM/Uniqueness.lean:454, and none of `CS7Data`, `CSoftData`,
`thm_C_S7`, `thm_C_soft`, `CuspLawC`, `CInheritsData`, `prop_anchor_values`, `AnchorValuesData`, `cornerPolygon` exists
in work/lean yet (consistent with the file compiling; they will clash the moment the corner lane / CV-R tail port
their copies — see 7.1).

## 7. Port plan (task 7)

Port as LIBRARY material now (D-F11/D-F14): everything except §5, which is declared and mapped only when rows 110/112
land.  Suggested module split (PLAN_FINAL.md §4, unit U-CM-ROWS), each a plain `namespace SM` file:

| module | content (assembled lines) | imports needed |
|---|---|---|
| `SM/CornerPolygon.lean` | §1 (131-186): `cp_cornerStateSum_compat`, `cornerPolygonSum`, `cornerPolygonSum_projection`, `cp_cornerStateSum_congr`, `cornerPolygon`, `cornerPolygon_projection`, `cornerPolygon_projection'`, `cornerPolygon_chamber` | `SM.CChamber` (+ `SM.Uniqueness` for `GenericPolygon`/`polygonProjection`/`chamber` if not re-exported) |
| `SM/AnchorValues.lean` | §2 (188-439) minus `cornerPolygon_soft_of` / `cornerPolygon_anchorValuesHypotheses_of` / `anchor_values_of` / companions IF `CSoftData` is not yet available; otherwise whole §2 | `SM.CornerPolygon`, `SM.AnchorsDefinition`, `SM.SoftGenericLemma`, `SM.Uniqueness`, the corner module defining `CSoftData` |
| `SM/CuspDeletionGeneric.lean` (or appended to `SM/DeletionInteriors.lean` next to `fused_interior_lift` / `DeletionEdgeLift`) | the 10 `cu_*` helpers (772-907) + the leaf `cusp_deletion_generic` (908-936) — pure accepted geometry, no dependency on rows 110/112 | `SM.CuspDefinition` (`cusp_cases`), `SM.DeletionIndices`, `SM.DeletedTuple`, `SM.DeletionInteriors`, `SM.GenericTopology` (`g1_common_interiors_remote`), `SM.ZeroTriples` (`mem_concurrenceTriples`, `concurrenceTriple_iff`), `SM.Segment` (`remote_endpoints`), `SM.GermSides`/WallGerm |
| `SM/Comparison.lean` | §3 (441-677): `TrianglesC`, `tri_*`, `trianglesC`, `cs3_*`, `uniquenessHypotheses_C_of`, `thm_comparison_of`, `thm_comparison_root_of`, `thm_comparison_polygon_of`; later the row `thm_comparison` | `SM.CornerPolygon`, `SM.AnchorValues` (for `cornerPolygon_soft_of`), `SM.Uniqueness`, `SM.HypR`, `SM.CS3`, `SM.CSilent`, `SM.EmbeddedRotation`, `SM.LinkPositiveLift`, `SM.CBProducts`, `SM.UniformRotation`, corner modules for `CS7Data`/`CSoftData`/`corner_values_i` |
| `SM/CInherits.lean` | §4 (679-997): `CuspLawC`, `ReversalLawC`, `CInheritsData`, `cu_cuspLawC_of`, `cor_C_inherits_of`; §6 examples; later the row `cor_C_inherits` | `SM.Comparison`, `SM.CuspDeletionGeneric`, `SM.Children`, `SM.GermSides` |

7.1 **§0 interface copies to DELETE and replace by imports** (the section `CornerInterfaces`, assembled 51-129, with its
`open Link`): `CS7Data` (58-69) and `CSoftData` (70-77) → `import` the corner lane's row-110 / row-112 modules (the names
then resolve to the accepted `SM.CS7Data` / `SM.CSoftData`, byte-identical shapes, verified above); `cvl_embedded_of_no_crossings`
(78-101) and `corner_values_i` (102-127) → `import` the corner lane's row-105 module (PROVED there, unchanged at port).
Until the corner modules land, these four copies must stay in whichever comparison module is ported first (they
compile against the accepted library alone); the moment the corner lane ports them, the copies become exact
duplicate declarations in `namespace SM` and MUST be deleted here (the compile will fail otherwise — the clash scan
in §6 confirms they do not exist yet).  The CV/R-tail copies `TrianglesC` (445-447), `CuspLawC` (684-696), `ReversalLawC`
(699-701): this lane OWNS row 128's bundle (PLAN_FINAL.md §6), so port them in `SM/Comparison.lean` (`TrianglesC`) and
`SM/CInherits.lean` (`CuspLawC`, `ReversalLawC`, `CInheritsData`) and make the tail import them — the tail's
edits are PLAN_FINAL.md §6 items 1-3 (replace its `CInheritsData` :907-933 by this lane's 12-field structure; keep its
`cor_C_inherits` placeholder until `SM/CInherits.lean` exists, then import; `CornerLawsAndSoftData`,
`corner_laws_and_soft_of`, `corner_laws_and_soft` unchanged — the §6 first `example` here certifies the three fields it
reads keep their types).  Whichever of the two lanes ports first defines the three Props; the other imports.

7.2 **Header.** Replace the module docstring (16-45) per module: drop the "Statements_FINAL / judge's decision /
Sketch A-B / Check:" provenance, keep the source lines (sm-5:461-476, sm-6:299-311, 313-372), the fixed names, the
policy mode sentence, the FR-CM references, and the D-F11/D-F14 sentence about §5.  The word `sorry` must not appear in a
ported module: reword line 25 ("The only remaining `sorry` bodies are the three ROW THEOREMS of §5 …" → "the three row
theorems are declared with rows 110/112") and line 999 (the §5 section header "`sorry` until rows 110 …"); the §5
docstrings "Body once row 112 lands: …" (1003, 1007-1008, 1014-1015) are deleted with §5 or become the one-liner's
docstring at mapping time.  Lines 1005/1012/1017 (the three `sorry` bodies) are NOT ported until rows 110/112 exist,
then read `anchor_values_of thm_C_soft`, `thm_comparison_of hR thm_C_S7 thm_C_soft`, `cor_C_inherits_of hR thm_C_S7 thm_C_soft`.
`#print` / `#eval` / `#check`: none in the file; the axiom probe copy stays in the scratchpad.

7.3 **Linter.** The 3 `unusedVariables` warnings (179 `cornerPolygon_chamber`, 197 `AnchorValuesHypotheses.chamber`,
200 `.soft`) are on `hn` binders inside ∀-types that mirror the accepted `UniquenessHypotheses` fields
(SM/Uniqueness.lean:37-38, 72-76) verbatim.  Recommended: `set_option linter.unusedVariables false` right after the
imports, exactly as SM/Uniqueness.lean:3 does — zero statement change.  Alternative (`_hn`) changes binder names of
frozen statements and breaks the verbatim parity with `UniquenessHypotheses`; not recommended.

7.4 **Disclosures to add to work/AUTHOR_NOTES.md before the rows are mapped** (PREREVIEW.md non-blocking; neither is
in the current FR-CM-1..17 list — grep confirms no FR-CM-3′ / FR-CM-9′ entry): FR-CM-3′ — `AnchorValuesData.zero/loop/loopZero/A_*`
quantify over every `ZeroAnchor m r` / `LoopAnchor m r` / `LoopAnchorZero m` without def:anchors' case conditions
(`Admissible m r`; `MinimalAdmissible (m+1) r ∧ 2 ≤ |r|`; `(m+1, r) = (4, 0)`), a PROVED generalisation of the printed
proposition; FR-CM-9′ — the premise `G1 (deleteVertex w.center j) →` of `CuspLawC` is implied by `w.CuspAt j`
(`g1_deleteVertex hf.2.1`), so the printed "when the deletion satisfies (G1)" domain is every simple cusp wall; the premise
is kept for fidelity to print and to `ALawfulData.cusp_law`.  Also record the keep-or-drop decision on
`CInheritsData.root_values` (FR-CM-13, already disclosed; `thm_comparison_root_of` remains as companion either way).

7.5 **Imports.** Drop `import SM.CS5` (compile-verified unused: a scratch copy without it compiles at 0 errors); it is
needed only by the CV/R tail.  The remaining 13 imports were not individually minimised; the per-module lists above are
the expected needs and should be confirmed at port by compiling each module.

7.6 **Row mapping (`work/lean/lean-declarations.json`).** `thm:comparison` → `SM.thm_comparison` and `cor:C-inherits` →
`SM.cor_C_inherits` are `pending` with the fixed names already recorded; `prop:anchor-values` is `pending` with NO
declaration yet — propose `SM.prop_anchor_values : AnchorValuesData` (this lane's §5).  Map all three only when rows 110
(`thm:C-S7`, pending) and 112 (`thm:C-soft`, pending) land, with their module names and `statement_sha256` computed then.
The `_of` theorems, `trianglesC`, `cusp_deletion_generic` and the helpers are library material (no row entry).

7.7 **Optional library addition** (PREREVIEW probe P5): the kernel-checked bijection
`∀ a ≠ softOldIndex j j, ∃ g, a = softParentEdge j g` could be added to SM/SoftParentEdges.lean as
`softParentEdge_surjective_ne_soft` if a consumer prefers the `∀ g, a = softParentEdge j g → …` reading of the `A_g`
clause to the accepted `∃!` shape.  Not needed by this lane.

## 8. Files

- `work/drafts/comparison/Comparison_Assembled.lean` — the assembled file (1052 lines).
- `work/drafts/comparison/assemble_comparison.py` — the assembly script (re-runnable; aborts on any violation).
- `work/drafts/comparison/ASSEMBLY_REPORT.md` — this report.
- Scratchpad (not part of the lane): `…/scratchpad/Comparison_axprobe.lean` (+ `#print axioms`), `Comparison_noCS5.lean`
  (import test), `clash_scan.py`, `verbatim_check.py`, `assembled_compile.log`, `unit_compile.log`.
