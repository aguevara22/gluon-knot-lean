# ASSEMBLY_REPORT.md — marked-product block, assembled module

Written 2026-09-14 04:10 UTC / 12:10am ET by the assembler subagent.

**Result:** `work/drafts/markedproducts/MarkedProducts_Assembled.lean` — 4966 lines, **zero occurrences of
the string `sorry`**, compiles with `cd work/lean && lake env lean ../drafts/markedproducts/MarkedProducts_Assembled.lean`
with **0 errors, 0 warnings, exit 0, 16 s wall** (17 s with the four `#print axioms` appended, on a /tmp copy).
Intended home: `work/lean/SM/MarkedProducts.lean` (does not exist yet; imports `SM.PolynomialBlock`,
`SM.ZeroLink`, `SM.Stack`, `CV.Axioms`, `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`).
md5 `dd657e6894aa3986ca3baaea9a9ed185`.

## 1. Axioms (`#print axioms`, /tmp copy `/tmp/asm/MP_axioms.lean`)

```
'SM.join'       depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
'SM.lowest'     depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
'SM.blocks'     depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
'SM.homflyrows' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
```
Exactly the required sets; **no `sorryAx`** anywhere. All non-standard axioms are the literature axioms
of `work/lean/axiom-policy.json` (`lp:lm`, `lit:homfly`, `lp:lm-uniqueness`).

## 2. Method

Each unit file was diffed against its base (`diff -u`): `U_L U_J5 U_J3 U_J4a U_B2 U_R1 U_R3a U_R4 U_R3b`
against `Skeleton_FINAL.lean`, `U_J4b` against `U_J4a`, `U_R2` against `U_J5`. A Python script
(`/tmp/asm/assemble.py`) parsed every hunk into edits, mapped the `U_J4b`/`U_R2` edits into skeleton
coordinates through their base's own edits (reconstructing `U_J4a` and `U_J5` from the skeleton first, as
a check — both byte-exact), de-duplicated the shared blocks, applied all edits to one copy of the
skeleton in a single pass, and then verified that (i) every hunk's added lines occur verbatim and
contiguously in the result and (ii) the result minus all inserted lines is exactly the skeleton minus
the 14 deleted lines listed below.

**Removed lines check.** Every unit diff removes only `  sorry` lines, except `U_R1`, which also
rewrites the first line of the docstring of `exists_markedInterval_of_mark`
(`(D9 sub-obligation; ANALYSED ONLY, PLAN_FINAL §5)` → `(D9 sub-obligation; PLAN_FINAL §5; PROVED, unit U-R1)`;
docstring only, statement unchanged). No unit changes a statement or a definition.

## 3. Hunk map (skeleton coordinates; "pos" = skeleton line; REPLACE = that `sorry` line replaced)

| unit | hunk | pos | action | lines added | content |
|---|---|---|---|---|---|
| U_J4a | 1 | after 387 | INSERT | 151 | §G.0 `RecordIso.ofOccComps/ofOccCompsEquiv/ofOcc/ofOccOfCard` block (before `namespace Record`) |
| U_J5 | 1 | after 538 | INSERT | 37 | helper `lastKeep_some_spec` |
| U_J5 | 2 | 549 | REPLACE | 126 | proof of `firstReturn_mul_swap_of_lastKeep_some` (J5) |
| U_J5 | 3 | 557 | REPLACE | 64 | proof of `firstReturn_mul_swap_of_lastKeep_none` (J6) |
| U_J3 | 1 | after 713 | INSERT | 341 | §U-J3 block: `RBasing.join` and its lemmas |
| U_J3 | 2 | 727 | REPLACE | 6 | proof of `exists_rUnderFirst_joinRecord` |
| U_J4b | 1 | after 728 | INSERT | 216 | §G.2b helpers (`sumKeepEquiv`, `SmoothInlKeep`, …) |
| U_J4b | 2 | 742 | REPLACE | 25 | proof of `exists_joinRecord_smooth_inl` |
| U_L | 1 | after 905 | INSERT | 22 | helper `eq_over_under_of_crossing_eq` |
| U_L | 2 | 913 | REPLACE | 16 | proof of L6 `mixedSignSum_switch_of_ne` |
| U_L | 3 | 923 | REPLACE | 60 | proof of L7 `mixedSignSum_switch_self` |
| U_L | 4 | 931 | REPLACE | 53 | proof of L8 `twoLambda_switch` |
| U_B2 | 1 | after 1424 | INSERT | 62 | §H.4a helpers (`sigmaSetUnionEquiv`, `sigmaSetSingletonEquiv`, …) |
| U_B2 | 2 | 1434 | REPLACE | 74 | proof of `IsCleanMarkedJoin.crossingEquiv` |
| U_B2 | 3 | 1442 | REPLACE | 23 | proof of `joinForest_sign` |
| U_R1 | 1a | 1444 | REPLACE | 371 | `namespace EdgeDisc` block (370 lines) + rewritten docstring line |
| U_R1 | 1b | 1449 | REPLACE | 122 | proof of `exists_markedInterval_of_mark` |
| U_R2 | 1 | after 1450 | INSERT | 227 | §U-R2 toolbox (incl. new def `Record.onePred`) |
| U_R2 | 2 | 1459 | REPLACE | 68 | proof of `isRealizable_restrictCrossings_of_gapContiguous` |
| U_R3a | 1 | after 1460 | INSERT | 727 | §U-R3a `steps`/`ArcBetween` toolbox + one-gap lemma |
| U_R3b | 2 (own part) | after 1460, after U_R3a's block | INSERT | 405 | §U-R3b parts (d)-(e): `gapMark`, `splitOcc`, consecutive block, join identity |
| U_R3b | 3 | 1475 | REPLACE | 37 | proof of `restrictCrossings_join_decomp` |
| U_R4 | 1 | 1490 | REPLACE | 132 | proof of `exists_joinForest_of_realizable` |

Deleted skeleton lines (14): 549, 557, 727, 742, 913, 923, 931, 1434, 1442, 1444 (R1 docstring line),
1449, 1459, 1475, 1490 — the 13 `sorry` chain lemmas plus the one docstring line. 1601 of 1615
skeleton lines are retained byte-for-byte, in order.

## 4. De-duplications

- **G.0 block** (151 lines, after skeleton line 387): present in `U_J4a`, `U_J4b` (inherited), `U_R3b`
  hunk 1. Verified byte-identical between `U_J4a` and `U_R3b`; included once.
- **U_R3a block** (727 lines, after skeleton 1460): `U_R3b` hunk 2 (1132 lines) was verified to be
  exactly U_R3a's 727 lines followed by U_R3b's own 405 lines (starting
  `/-! ### Unit U-R3b — R3 parts (d)-(e) …`); the 727 lines included once, in the same order.
- **U_J5 proofs/helper**: `U_R2` inherits them (diffed against `U_J5`); included once.
- **Renames: none needed.** 309 declarations in the assembled file, 0 duplicate fully-qualified names
  (checked by a namespace-tracking scan; Lean also reported no "already declared" error).

## 5. Byte-identity with `work/drafts/MarkedProducts_statement.lean`

`structure JoinData / LowestData / BlocksData / HomflyRowsData : Prop where …` blocks (including
field docstrings) are byte-identical (16/14/21/22 lines; assembled L288/L311/L333/L361). The headers
`theorem join : JoinData`, `theorem lowest : LowestData`, `theorem blocks : BlocksData`,
`theorem homflyrows : HomflyRowsData` (text before `:=`/`where`) are byte-identical (assembled
L4933/L4939/L4945/L4952; the statement file has `:= by sorry`, the assembled file `where`).
Bonus check: all 21 other declarations of the statement file (`Diagram.IsGapOf`, `MarkedDiagram`,
`IsCleanMarkedJoin`, `knotRestrict`, `twoLinking`, `twoLambda`, `steps`, `ArcBetween`, `Interlaces`,
`interlacementGraph`, `CrossKeep`, `restrictCrossings`, `BlockSupply`, `JoinForest`, `IsSplitUnion`,
and the accompanying theorem headers) occur verbatim in the assembled file.

## 6. Name clashes with `work/lean`

A namespace-tracking scan of all 612 `.lean` files under `work/lean` (SM, CV, Bridge, RProof,
Supplemental) against the 309 fully-qualified names of the assembled file: **0 exact clashes**. The
195 declarations new relative to the skeleton (171 theorems, 23 defs, 1 instance) share a short name
with a `work/lean` declaration in 20 cases, all in different namespaces (18× `SM.Link.EdgeDisc.*` vs
`SM.Link.Smoothing.*` — `pt`, `others`, `r₁`, `disc`, `isDisc_disc`, …; `SM.Link.IsRealizable.smooth`
vs `Record.smooth`/`RecordIso.smooth`; `SM.Link.Record.exists_gap` vs `SM.NoClosedHalfPlane.exists_gap`).
Not clashes; noted only because `open` of both namespaces at once would make them ambiguous.

New definitions introduced by units (all new names): `RecordIso.ofOccComps`, `.ofOccCompsEquiv`, `.ofOcc`,
`.ofOccOfCard` (J4a); `Record.RBasing.join` (J3); `Record.sumKeepEquiv`, `Record.SmoothInlKeep` +
its `DecidablePred` instance (J4b); `sigmaSetUnionEquiv`, `sigmaSetSingletonEquiv` (B2);
`EdgeDisc.pt/others/r₁/rad/disc/ρ/θlo/θhi/arc` (R1); `Record.onePred` (R2); `Record.PosBetween`,
`Record.Alternates` (R3a); `Record.gapMark`, `Record.splitOcc` (R3b).

## 7. Deviations from "units verbatim"

1. Five comment lines were reworded so the file contains no occurrence of the string `sorry` at all
   (the requirement was "ZERO `sorry`"; these were stale prose, not statements or proofs):
   - L36 (module header): `Every \`sorry\` below is a chain lemma listed in PLAN_FINAL.md §3 with its unit.`
     → `Every chain lemma listed in PLAN_FINAL.md §3 is proved below by its unit (assembled 2026-09-14).`
   - L2514 (§H.4 header): `analysed; the chain lemmas are \`sorry\`)` → `analysed; the chain lemmas are
     proved by units U-B2, U-R1, U-R2, U-R3a/b, U-R4 below)`
   - L3516 (U-R3a header) and L4243 (U-R3b header): `every lemma is sorry-free` → `every lemma is fully proved`
   - L4943 (docstring of `theorem blocks`): `through the analysed chain of §H.4, left \`sorry\`;` →
     `through the chain of §H.4, now proved;`
2. `U_R1`'s own docstring rewrite of `exists_markedInterval_of_mark` (see §2) is kept as the unit wrote it.
3. Left untouched (flag for the parent): three chain-lemma docstrings still carry the skeleton's
   `ANALYSED ONLY` wording although the lemmas are now proved — L3436
   `isRealizable_restrictCrossings_of_gapContiguous`, L4645 `restrictCrossings_join_decomp`,
   L4697 `exists_joinForest_of_realizable`. Docstrings only; one-word edits if wanted.
4. Nothing under `work/lean` was written; the module has not been installed as `SM/MarkedProducts.lean`.

## 8. Verification commands

```
cd work/lean && source /workspace/envs/lean/env.sh
lake env lean ../drafts/markedproducts/MarkedProducts_Assembled.lean      # 0 errors, 0 warnings, 16 s
grep -c sorry ../drafts/markedproducts/MarkedProducts_Assembled.lean       # 0
python3 /tmp/asm/assemble.py     # re-derives the file from Skeleton_FINAL + unit diffs, prints checks
python3 /tmp/asm/bytecheck.py    # bundles / headers vs MarkedProducts_statement.lean
python3 /tmp/asm/fqn.py          # FQN clash scan vs work/lean
```
