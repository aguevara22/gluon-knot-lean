# ASSEMBLY_REPORT — cb lane, row 102 cb:products (`SM.cb_products`)

Assembler, 2026-09-14 (~07:00 UTC / 3:00am ET). Output: `work/drafts/cb/CBProducts_Assembled.lean` (1937 lines).
Compile: `cd work/lean && lake env lean ../drafts/cb/CBProducts_Assembled.lean` → **0 errors, exit 0** (14.5 s).
`grep -c sorry work/drafts/cb/CBProducts_Assembled.lean` → **0**. All 18 leaves of the skeleton are proved; nothing
is left unproved.

## 1. Unit diffs against `Skeleton_FINAL.lean` (all seven verified, no violations)

Method: `diff Skeleton_FINAL.lean U_<unit>.lean` for each unit, plus a script check (`/tmp/cbasm/assemble.py`) that
(a) the unit file is byte-identical to the skeleton before its own `/-! ### <unit>` header and from the next unit's
header to EOF, and (b) every non-placeholder line of the skeleton's block for that unit appears verbatim in the unit's
block (statement frozen). Removed lines per unit are exactly the `:= sorry` tails of that unit's own leaves:

| unit | skeleton lines removed | added | leaves replaced | helpers added (all prefixed) | structural additions |
|---|---|---|---|---|---|
| KL0 | 9 (`gaussSucc`, `gaussSucc_val`, `gaussPair`, `gaussPair_val`, 4 fields of `gaussRecord`, `label_crossingOf`) | 87 | 9 | 6 `kl0_*` | 2× `omit [NeZero n] in` (per-declaration) |
| KL1 | 2 (`positiveLiftRecordIso`, `positiveLiftRecordIso_val`) | 770 | 2 | 48 `kl1_*` | 1× `omit … in` |
| KL2 | 1 (`gaussRecord_adj_iff`) | 174 | 1 | 13 `kl2_*` | 1× `omit … in` |
| KL3 | 2 (`gaussRecord_restrict_iso`: the `:=` line got ` by`, the lone `sorry` line went) | 188 | 1 | 8 `kl3_*` | `section kl3_helpers` … `end kl3_helpers` with a local `variable {α β : Type*} [DecidableEq α]` (closed) |
| T1 | 1 (`restrictCrossings_iso_of_recordIso`) | 20 | 1 | 1 `t1_*` | none |
| GL | 1 (`exists_blockGraphEquiv`) | 318 | 1 | 35 `gl_*` | `section GLHelpers` … `end GLHelpers` with a local `variable {S : Finset (Crossing P)}` (closed); `omit hn hP in` per declaration |
| AS | 2 (`mem_blockRecordCrossings_crossingOf`, `exists_visit_of_mem_carrierCrossings`) | 22 | 2 | 0 | none |

No statement, definition, name or docstring of the skeleton was changed by any unit; no unit touched another unit's
block, the glue, the row theorems or the companion lemmas. Every `variable`/`section` a unit added is closed inside its
block, so nothing leaks into the frozen code that follows. All unit hunks were adopted.

## 2. What was removed (already in `work/lean/SM/CBBlocks.lean`, built as `SM.CBBlocks`)

Verified byte-identical before removal (substring test of the skeleton text against CBBlocks.lean):

* Skeleton lines 21–237 (`namespace CB` … `structure CbProductsData … no_blocks …`, 217 lines, docstrings included):
  `SM.CB.cg`, `mem_Ind`, `geoIndependent`, `someVisit`, `someVisit_crossing`, `crossingOwner`, `blockOwner`,
  `blocksOwnedBy`, `carrierPoly`, `IsBlockCarrierDiagram`, `blockRecordCrossings`, `blockRecord`, `recordPolynomial`,
  `recordPolynomial_eq`, `blockPoly`, `end CB`, `open CB`, the `variable` line, `SM.CbBlocksDefinitionData`,
  `SM.CbProductsData` — found verbatim in CBBlocks.lean:118–332.
* Skeleton lines 513–533 (`theorem cb_blocks_definition … equals_Hplus _ := ⟨P_eq_homfly _, P_eq_homfly _⟩`): found
  verbatim in CBBlocks.lean:336–355. Only its one-line docstring differs between the two files (skeleton: "assembled
  (every field an accepted fact)"; CBBlocks: "(DEFINE row), on the printed binder …"); the docstring went with the
  theorem, the declaration text is identical.

Not removed (not in CBBlocks): everything from the chain header on — the KL0 definitions (`gaussList`, `gaussSucc`,
`gaussPair`, `positiveOverBit`, `gaussRecord`, `gaussRecord_M`, `gaussRecord_componentCount`, `occVisit`,
`occVisit_mem`, `label`, `label_mem`), all leaves, PC (`exists_blockCarrier`), the glue section, `cb_products`,
`greedy_independent`, `greedy_step`.

## 3. Shape of `CBProducts_Assembled.lean`

```
import CV.X1 / CV.PieceCurve / SM.MarkedProducts / SM.CornerStateSum   (the skeleton's imports)
import SM.CBBlocks                                                    (new)
/-! # CBProducts … -/                                                 (new module header, replaces the skeleton's)
namespace SM
open SM.Carrier SM.GeoCarrier SM.Link
attribute [local instance] Classical.propDecidable                    (skeleton 15–19, kept: the local instance does
                                                                       not travel with the import)
/-! ## Chain … -/  (skeleton 238–244; one phrase reworded to drop the placeholder word)
namespace CB
variable {n : ℕ} [NeZero n] {P : LabelledTuple n}                     (skeleton 246–248)
KL0 block (from U_KL0)  KL1 block (U_KL1)  KL2 (U_KL2)  KL3 (U_KL3)  T1 (U_T1)  GL (U_GL)  AS (U_AS)
PC + section Glue … end Glue + end CB + open CB + variable            (skeleton 385–510, byte-identical)
theorem cb_products … (skeleton 534–575, byte-identical incl. docstring; header
  `theorem cb_products (hS : IsDecomposition hn hP S) : CbProductsData hn hP hS where` unchanged)
companion lemmas greedy_independent / greedy_step, end SM             (skeleton 577–609, byte-identical)
```

`open`/namespace fix-up: none needed beyond the import. The chain re-enters `namespace CB` itself (skeleton line 246),
so the `SM.CB` definitions of CBBlocks resolve unqualified there, and the skeleton's own `open CB` (line 508) covers
`cb_products`. Diff checks: the region from `/-! ### PC` to the Row-102 docstring and the region from the Row-102
docstring to EOF are byte-identical to the skeleton (`diff` empty).

Prose mentions of the placeholder word: the skeleton had two (module header line 10, chain header line 238). The
module header was rewritten; in the chain header "sorried leaves by unit, then the row theorems assembled from them"
became "the leaves by unit (all proved), then the row theorem assembled from them". No unit file added any.

## 4. Compile and axioms

`cd work/lean && lake env lean ../drafts/cb/CBProducts_Assembled.lean`: 0 errors, exit 0, 14.5 s wall. Four warnings,
all pre-existing in the frozen skeleton text (the same four the units reported):
* :83 `gaussPair` — "Variable name `hc` is not explicitly referenced" (frozen statement binder);
* :87 `gaussPair_val` — "automatically included section variable(s) unused: [NeZero n]" (frozen statement);
* :1739 `exists_blockCarrier` — unused `hT` in the `∃` binder (frozen PC statement);
* :1811 glue `record_iso_blockRecord` — `Set.mem_setOf_eq` deprecated (→ `Set.mem_ofPred_eq`).
No `declaration uses sorry` warning anywhere.

`#print axioms` on a /tmp copy (`/tmp/cbasm/axioms_check.lean` = the file + `#print axioms` lines; log
`/tmp/cbasm/axioms.log`):

| declaration | axioms |
|---|---|
| **`SM.cb_products`** | **`propext, Classical.choice, Quot.sound, SM.lp_lm`** |
| `SM.CB.product_of_chain` | `propext, Classical.choice, Quot.sound, SM.lp_lm` |
| `SM.CB.positiveLiftRecordIso`, `positiveLiftRecordIso_val`, `gaussRecord_adj_iff`, `gaussRecord_restrict_iso`, `restrictCrossings_iso_of_recordIso`, `exists_blockGraphEquiv`, `mem_blockRecordCrossings_crossingOf`, `exists_visit_of_mem_carrierCrossings`, `exists_blockCarrier`, `record_iso_blockRecord` | `propext, Classical.choice, Quot.sound` |
| `SM.greedy_independent`, `SM.greedy_step` | `propext, Classical.choice, Quot.sound` |
| `SM.cb_blocks_definition` (imported, for comparison) | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` |

Against the expected list (`propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm`, possibly
`SM.lp_lm_uniqueness`): `SM.cb_products` uses a strict subset — `SM.lp_lm` only (through the accepted `SM.blocks`
product law in `product_of_chain`, as PLAN/Statements predicted: "row 102 adds `SM.blocks`' axioms (`SM.lp_lm`)").
`SM.lit_homfly` and `SM.lp_lm_uniqueness` do not enter: row 102 never mentions `homfly`/`P_eq_homfly` (those are
row 101's `equals_Hplus`). `SM.lp_lm` is a registered literature interface in `work/lean/axiom-policy.json`
(`"lp:lm": "SM.lp_lm"`). **No `sorryAx`.**

## 5. Name-clash scan over work/lean

Script `/tmp/cbasm/clash_scan.py` (namespace-aware: tracks `namespace`/`section`/`end`, top-level
theorem/def/abbrev/structure/instance/…; log `/tmp/cbasm/clash_scan.log`). The assembled file declares 146 top-level
names (143 in `SM.CB`, 3 in `SM`: `cb_products`, `greedy_independent`, `greedy_step`), no internal duplicates.
Scanned 636 modules / 11,599 declarations under `work/lean` (excluding `.lake`).

**Fully-qualified clashes: 0.**

Informational (same short name, different namespace; not clashes, and both compile together today because inner
namespace resolution wins inside `namespace SM.CB`):
* `SM.CB.gaussList` vs `SM.gaussList` (`work/lean/SM/GaussWord.lean:20`, the P-level Gauss list of def:gauss-word);
* `SM.CB.label` vs `SM.PolygonDiagram.label` (`work/lean/SM/Rounding.lean:98`).
A future module that does `open SM.CB` next to `open SM.PolygonDiagram` and then writes bare `label` would need to
qualify.

## 6. Unproved leaves / own proving

None. All 18 skeleton leaves (KL0 ×9, KL1 ×2, KL2, KL3, T1, GL, AS ×2) arrived proved; no proving was needed on my
side. Not a leaf and therefore not added (frozen file): `blockPoly_eq_of_labels_eq` (PLAN §6, for cb:singleton) — the
KL3 report §"For the executor" records how to state it from `gaussRecord_restrict_iso` + `record_iso_blockRecord`
when cb:singleton is taken up.

## 7. For the porter (SM/CBProducts.lean)

* Copy `CBProducts_Assembled.lean` to `work/lean/SM/CBProducts.lean` unchanged except the module header's
  "Checked with" path. `import SM.CBBlocks` is already in place; the skeleton's four imports are all redundant with
  CBBlocks' closure (`CV.X1` imports `CV.PieceCurve`, which PC's `CV.pieceSupport`/`CV.pieceCarrier` come from) but
  were kept as the task asked — harmless, and they document the dependencies.
* Row declaration to register: `SM.cb_products : CbProductsData hn hP hS`; axioms `propext, Classical.choice,
  Quot.sound, SM.lp_lm`.
* The four warnings above are in frozen statement text; silencing `gaussPair`'s `hc` (→ `_hc`) or adding
  `omit [NeZero n] in` before `gaussPair_val` would change frozen lines and is a porter's/judge's call, not mine.
