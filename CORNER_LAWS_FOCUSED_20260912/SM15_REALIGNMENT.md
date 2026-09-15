# Frame SM15 realignment of this package — 2026-09-12

The previous execution used frame SM12. The author re-issued the source as
frame SM15 (frozen 2026-09-12) after the previous executor found that
`lem:shift` clause (iii) was false off the generic locus. This package was
realigned from SM12 to SM15 in place so that all existing work continues.
Nothing under work/lean/SM, work/checks, work/checkpoints, work/reports or
work/decisions was changed; the accepted map keeps all 39 rows.

## Bundle layer

- reference/SM/sm-0-legend.tex, sm-1-polygons.tex, sm-2-amplitude.tex and sm.tex
  are the SM15 bytes (sm-3, sm-4, sm-5, sm-6, sm-refs.bib unchanged; R/ and
  BRIDGE/ context unchanged). provenance/SM15 holds the SM15 manifest;
  provenance/SM12 is the historical pin the earlier reviews bound to.
- blueprint/ regenerated on SM15 with the same instrument: same 172 source rows,
  same 19 R/bridge/final obligations, same EXECUTION.json targets, axiom policy
  and TARGETS.md; 40 rows have new line numbers; new reference edges
  lem:crossing-test→lem:g1, lem:shift→def:regular, lem:shift→lem:g1,
  prop:A-chamber→prop:chambers (ORDER.md changed accordingly).
- Bridge quotations: QUOTATIONS.json is sealed SM11 text. The pinned ledger
  provenance/BRIDGE_REALIGNMENT_SM15.json records each of the 59 quotations as
  exact (46), relocated unchanged (11) or superseded by SM15 wording (2: SM_G1,
  SM_CROSSINGS) with the replacement span hashed. verify_bundle.py checks it.
- ERRATUM_20260912.md, CHANGES_SINCE_20260909.md and DIFF_SM12_to_SM15.txt are
  the author's record of the change. Read them before working on the rows below.

## Source statements whose formal content changed (CHANGES_SINCE_20260909.md, section 1)

| row | SM15 change | state in this package |
|---|---|---|
| `lem:shift` (iii) | ℓ(P̄) = n − ℓ(P) − z(P), z = number of zero turns; ℓ(P̄) = n − ℓ(P) for generic P | pending; NOW PROVABLE AS PRINTED. The SM12 counterexample (work/repairs/ShiftZeroTurn.lean, reviewed in work/reviews/lem-shift-scope.md) is the erratum the author fixed. Prove all four clauses on SM15; `SM.shift_reversal_corrected` in work/lean/SM/ShiftReversal.lean is a usable helper. |
| `lem:shift` (iv) | stated for P in the regular locus, with σP and P̄ regular | same row |
| `lem:g1` (iv) | "two distinct adjacent edges" | accepted; `SM.g1` already states i ≠ j. Re-read recorded in work/reviews/lem-g1.json; countersign requested. |
| `prop:A-chamber` | "constant on every labelled chamber (the root fixed)"; proof cites prop:chambers | accepted; `SM.A_chamber`'s labelled-chamber conjunct is exactly this. Re-read recorded; countersign requested. |
| `lem:softvertex` | hypotheses added: P generic, q admissible, 0 < ε < ε₀ of lem:soft-generic | pending; transcribe the SM15 statement when you reach it. |
| `lem:chi-basic` (iii) | wording only: left/right naming stated as a convention for a nonzero edge | accepted; re-read recorded; countersign requested. |

Tag-only changes (status tags, no wording change): `lem:crossing-test`,
`lem:rot`, `lem:gates-nonzero`. Every other accepted row has byte-identical
statement text at a new line number.

## What was refreshed in work/

- work/lean/lean-declarations.json: `line` refreshed for every source row from
  the SM15 blueprint (41 rows); `sm15_note` added to `lem:shift`. No status,
  declaration, statement hash or reviewer changed.
- Every accepted row's review file: `source_sha256` now hashes the SM15 file, and
  a `source_realignment` block records the SM12 hash and line, the SM15 hash and
  line, and the byte comparison of the two statement excerpts (32 identical,
  3 tag-only, 3 wording-changed). The three wording-changed rows carry a
  `re_review` by an independent AI reviewer of a different model family
  (Claude; no authorship of any Lean statement) and a countersign request.
- work/SM15_REALIGNMENT.json: the per-row ledger of the above.
- The previous executor's checkpoint receipts (work/checkpoints; the
  work/checks/checkpoint-* dumps are not in the shipped copy) hash-bind the
  SM12 reference files and the old metadata; they describe the state at their own time and are not expected
  to match the current bytes. The current checker receipt is
  work/checks/stage-development.json.
