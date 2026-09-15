# ASSEMBLY_REPORT — prop:C-chamber (work/drafts/cchamber/CChamber_Assembled.lean)

Assembled 2026-09-13 23:04 UTC / 7:04pm ET by the assembler subagent (Lean v4.34.0-rc2, Mathlib pin).

## Result
- `CChamber_Assembled.lean`: 1384 lines, 99 declarations (skeleton: 678 lines, 84 declarations).
- `cd work/lean && lake env lean ../drafts/cchamber/CChamber_Assembled.lean`: **exit 0, no output**
  (no errors/warnings/`sorry`). Wall 7 s on the 8-vCPU pod (imports built; `#print axioms` copy: 6 s).
- `sorry`: **0** proof occurrences (the word appears twice in the module docstring prose only).
- `#print axioms SM.C_chamber` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` (as required;
  `lit_homfly` enters through `homfly` in def:C).

## Merge method
Each unit is a copy of `Skeleton_FINAL.lean` with proofs in place, so `diff Skeleton_FINAL.lean U*.lean`
gives, per unit, only `NcM,K` hunks (a single `  sorry` line replaced) and `NaM,K` hunks (helpers
inserted). The script `/tmp/asm/merge.py` parsed the six diffs, asserted every `c` hunk replaced a bare
`sorry` line, asserted all hunks touched pairwise-disjoint skeleton lines, and re-emitted the skeleton
with the hunks applied: **49 replacements + 7 insertions**. The 50th skeleton `sorry`
(`leftTurns_transport`) is the recorded fix below.

| unit | sorries replaced | helpers / other insertions (placed where the unit placed them) |
|---|---|---|
| U1a | 9 | none |
| U1b | 11 | `zmod_val_cast`, `zmod_cast_cast` (after `recastTuple_rfl`); `isRotated_filter_map_of_forall`, `getElem_eq_map_of_eq`, `getElem_eq_map_of_rotate_eq` (before `componentMarkList_transport`) |
| U2 | 7 | `include τ in leftTurns_eq_of_transport` (after the §1d index-set lemmas) |
| U3 | 13 | `turn_recastTuple_cast` (start of `section PathTransport`); `omit [NeZero n] in` before `generic_family_crossingParameterOrderAgrees` and before `continuous_path_crossingPoint` |
| U4 | 3 | none |
| U5 | 6 | `import SM.SortedCut`; `Shadow.single_pt_ext`, `def shiftStrandMap`, `section ShiftReparam` (`shiftStrandMap_toFun`, `shiftStrandMap_surjective`, `shiftPullback`, `shiftPullback_eq_positiveDiagram`, `shiftPullback_overVisit_snd`, `shiftReparamData`) between `positiveDiagram_single_recast` and `reparam_positiveDiagram_single_shift` in `namespace Link` |

## De-duplication
Nothing to de-duplicate: no helper name occurs in two units, none clashes with `work/lean/SM` (grep),
the assembled file has no duplicate declaration names, and `import SM.SortedCut` (U5) introduced no clash.

## The `leftTurns_transport` fix (PLAN_FINAL.md §5 addendum)
The skeleton's `theorem leftTurns_transport : leftTurns Q = leftTurns P` did not mention `τ`, so it did
not take the transport (variable-inclusion rule) and was false as stated. Assembled as U2/the plan
prescribe: U2's helper `include τ in theorem leftTurns_eq_of_transport` is kept, followed by
`include τ in theorem leftTurns_transport : leftTurns Q = leftTurns P := τ.leftTurns_eq_of_transport`.
Checked: `#check @SM.Carrier.MarkTransport.leftTurns_transport` now has argument
`(τ : MarkTransport hn hP hQ)`. `cornerStateSum_transport` uses the helper (as in U2). Dropped from the
assembled module: U2's explanatory NOTE and the counterexample theorem
`leftTurns_transport_false_as_stated` (not part of the chain; still on record in U2.lean). Gotcha met:
a doc comment cannot precede `include τ in` — the modifier goes first.

## Statement changes
- Only the recorded `include τ in`; every other fixed statement/definition is the skeleton's text. Inherited
  from U3 (recorded): two `omit [NeZero n] in` prefixes drop the unused instance argument from
  `generic_family_crossingParameterOrderAgrees` and `continuous_path_crossingPoint` (uses resolve by unification).

## Row statement block vs work/drafts/CChamber_statement.lean
- `/-- prop:C-chamber as printed ... -/ structure CChamberData : Prop where ...`: **byte-identical**.
- `theorem C_chamber : CChamberData`: signature identical; the statement file has `:= by sorry`, the
  assembled file has `where constant := by ...` (the skeleton's closed descent proof).
- Module docstring: the statement file's `/-! Source prop:C-chamber ... -/` text is reproduced **verbatim
  as the prefix**; appended after it: an "Assembly provenance (2026-09-13)" paragraph and the skeleton's
  route/instances/descent paragraphs (with its sentence "Every lemma of the chain is stated; `sorry` marks
  the obligations..." reworded to "Every lemma of the chain is proved; `SM.C_chamber` is proved from the
  chain."). No other difference.
- Imports: statement file has `SM.CornerStateSum`, `SM.Chambers`; assembled adds the skeleton's 10 and U5's
  `SM.SortedCut`. `namespace SM` / `open Link Carrier` agree; skeleton's local `Classical.propDecidable` kept.
