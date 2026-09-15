# ASSEMBLY_REPORT — cf:lem-rounding (Rounding_Assembled.lean)

Assembler run 2026-09-14 05:00 UTC / 01:00am ET, on the home pod.
Output: `work/drafts/rounding/Rounding_Assembled.lean` (3147 lines, md5 017228dfbe2a1906f19dba9385b94682).
Script: `work/drafts/rounding/assemble_rounding.py` (re-runnable; it re-derives the file from
`Skeleton_FINAL.lean` + `U_{P,A,G1,G2,G3,E,X}.lean`, exits 1 on any violation).
Check: `cd work/lean && lake env lean ../drafts/rounding/Rounding_Assembled.lean` — exit 0, **0 errors, 0 warnings**, 8.7 s.
Nothing was written under `work/lean`; `lake build` was not run.

Inputs (md5): Skeleton_FINAL d752c5611eac8c641dcdc6ecdab1e184, Rounding_statement_FINAL 34cda177ed48ac698833321146787a09,
U_P f1efa1e7…, U_G1 6229cbcb…, U_E bef7a43a…, U_A ed98f961…, U_G2 b2b11b81…, U_G3 da41b672…, U_X ac8c748e….

## 1. Unit diffs against the skeleton (task 1)

For every unit, `diff Skeleton_FINAL.lean U_<u>.lean` removes only lines that are exactly `  sorry`, and
`assemble_rounding.py` additionally checked, per removed line, that the enclosing `theorem` is one of that
unit's leaves (PLAN_FINAL §5 split), and, per added line, that it contains none of
`axiom|sorry|native_decide|unsafe|implemented_by|set_option|opaque` and that every added declaration is a
`theorem` carrying the unit prefix (`P_` helpers are `private theorem`).

| unit | leaves proved | sorries removed | lines added | helpers | skeleton hunk range |
|---|---|---|---|---|---|
| P  | 4  | 4  | 73  | 2 (private) | 598–615 |
| A  | 7  | 7  | 383 | 27 | 630–695 |
| G1 | 3  | 3  | 65  | 5  | 706–739 |
| G2 | 10 | 10 | 307 | 26 | 766–870 |
| G3 | 4  | 4  | 90  | 5  | 910–938 |
| E  | 9  | 9  | 332 | 33 (the U_E report says 34; 33 distinct `E_` headers exist) | 947–980 |
| X  | 15 | 15 | 652 | 41 | 990–1068 |
| **total** | **52** | **52** | **1902** | **139** | — |

52 = all leaf sorries of the skeleton (lines 598–1068). **No violation found in any unit**: no statement,
definition, name or docstring changed; all edit ranges are pairwise disjoint in skeleton coordinates
(so the hunks compose without conflict). Helper names are all distinct (unit prefixes), so no
de-duplication or renaming was needed (`dedup_notes: []`). Note: `P_iteratedDeriv_eq_zero_of_eqOn_open`
(private) and `X_iteratedDeriv_eq_zero_of_eqOn_open` are two independent helpers with similar roles under
different names; both kept (harmless).

## 2. Assembly (task 2)

`assemble_rounding.py` computes each unit's line diff against the skeleton (difflib, autojunk off), sorts
the 61 disjoint edits, applies them in one pass, then verifies:
* every inserted block occurs contiguously in the result (61/61);
* every skeleton line except the 52 removed sorries survives in order;
* every one of the 150 skeleton declaration blocks (header + body, minus the trailing `  sorry`) and every
  one of the 214 skeleton paragraphs (docstring + declaration + body, minus `  sorry`) occurs verbatim and
  contiguously in the assembled file (checked by `/workspace/scratch/rounding_asm/check_headers.py` and an
  inline paragraph check) — i.e. no helper was inserted inside a header or between a docstring and its
  declaration.

The assembled file is exactly: skeleton text, byte for byte, with the 52 `  sorry` lines replaced by the
units' proofs and the 139 helpers inserted at the units' positions (all inside `namespace CornerRounding`,
in `section`s `global`/`discs`/`doubles` or the preceding unsectioned block).

## 3. Unproved leaves (task 3)

**None.** All 52 leaves are proved; no `sorry` remains in any declaration.

## 4. Compile, sorry count, axioms (task 4)

* `cd work/lean && lake env lean ../drafts/rounding/Rounding_Assembled.lean`: exit 0, no diagnostics at all
  (0 errors, 0 warnings — in particular no `declaration uses sorry`).
* `grep -c sorry Rounding_Assembled.lean` = **2**, both prose inherited verbatim from the skeleton:
  line 15 (module docstring "…the chain of leaf lemmas (§8, `sorry`)…") and line 569 (section header
  "## 8. The chain of lemmas (all `sorry`; …)"). No `sorry` token inside any declaration. These two comments are
  now stale; I left them untouched so the file is exactly skeleton + hunks — the promoter may reword them.
* `/tmp/Rounding_Assembled_axioms.lean` (= the assembled file + `#print axioms`):
  * `'SM.cf_lem_rounding' depends on axioms: [propext, Classical.choice, Quot.sound]`
  * `'SM.CornerRounding.roundedWitness' depends on axioms: [propext, Classical.choice, Quot.sound]`
  No `sorryAx`; matches the `standard` list of `work/lean/axiom-policy.json`.

## 5. Byte-identity with Rounding_statement_FINAL.lean (task 5)

* Statement lines 54–435 (`namespace SM` … through `RoundingData.of_diagram`, i.e. `PolygonDiagram`,
  `eucDist`, `cornerDisc`, `subsegOut/In`, `polygonImage`, `SmoothRegularLoop`, `Carried`, `RoundingWitness`
  and its namespace, `RoundingData`, `RoundingData.of_diagram`, all docstrings) are byte-identical to
  assembled lines 60–441 (`diff` of the two ranges: only the expected divergence at statement line 436,
  the `/-- cf:lem-rounding. -/` docstring, vs the skeleton's "## 7. The construction" section header).
* `theorem cf_lem_rounding : RoundingData` — header identical; the statement's `:= by sorry` is the skeleton's
  `where …` body (assembled line 3125). The theorem docstring differs from the statement's one-liner exactly
  as in the judged skeleton (skeleton decision, not an assembly change).
* Statement lines 1–53 (imports + prose) differ only by the skeleton's 4 extra Mathlib imports and the
  "SKELETON:" sentence in the module docstring, as in Skeleton_FINAL.
* Main declaration name `SM.cf_lem_rounding` unchanged; `work/lean/lean-declarations.json` row
  `cf:lem-rounding` is still `pending` with empty `declaration`/`module` (to be filled at promotion).

## 6. Fully-qualified clash scan of work/lean (task 6)

`/workspace/scratch/rounding_asm/clash_scan.py`: a namespace-tracking parser (namespace/section/end,
block comments, structure fields) applied to the assembled file (373 fully-qualified names incl. structure
fields; 139 new helpers, all `SM.CornerRounding.*`) and to all 622 `.lean` files under `work/lean`
(excluding `.lake`; 11,942 declarations). **0 fully-qualified clashes.**
Sanity: the parser resolves e.g. `SM.turnlift` (SM/TurnLift.lean:628), `SM.regular_adjacent_meet`
(SM/CS3.lean:84), `SM.Link.PolyComp` (SM/LinkDiagram.lean:61).

Informational only (not clashes; all three are skeleton/statement names, not unit helpers) — last-component
coincidences that could become ambiguous in a downstream file that `open`s both namespaces:
`SM.CornerRounding.turn` vs `SM.turn` (SM/Chirotope.lean:13); `SM.CornerRounding.Admissible` vs
`SM.Admissible` (SM/Admissible.lean:10, a def); `SM.RoundingWitness.T` vs `SM.Link.T` (SM/LinkLaurentRing.lean:82).
Also from U_X_REPORT: `SM.regular_adjacent_meet` (SM/CS3.lean) is not in the import closure, so Unit X
reproved it as `X_regular_adjacent_meet`; no clash.

## 7. Hand-off

Ready for review/promotion: `work/drafts/rounding/Rounding_Assembled.lean`. To re-derive:
`python3 work/drafts/rounding/assemble_rounding.py` (prints a JSON summary; nonzero exit on violation).
