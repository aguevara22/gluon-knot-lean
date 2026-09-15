# One accept cycle, step by step (worked example: lem:shift, 2026-09-12)

This is the whole process for one unit of work, as the checker enforces it.
Do it for every claim and every definition, one at a time.

1. Pick the unit: `python3 tools/claims.py --next` (or the first tractable
   pending row of `--pending-only` in document order). Read the source around
   it in reference/ (blueprint/STATEMENTS_AND_PROOFS.md has the exact extract).
2. Search work/checks for an existing candidate for the row first
   (`grep -l '<row label or key words>' work/checks/*.body.lean`; the receipts
   `*-prototype-result.json` say which kernel session checked it). Port a usable
   body into a new module under work/lean/SM/ (one main declaration per source
   row; helpers allowed) instead of rewriting it. Transcribe the statement faithfully; prove it with
   zero sorry. `cd work/lean && lake build SM.<Module>` until it compiles.
   Example: work/lean/SM/ShiftTheorem.lean, main declaration
   `SM.shift_reversal`.
3. In work/lean/lean-declarations.json set the row's `declaration`, `module`
   and `status: "implemented"`. Run `python3 tools/check_lean.py work/lean`.
   It builds the mapped modules, rejects sorry and unregistered axioms, and
   writes work/checks/declaration-audit.json; the row's statement hash is
   `statement_hashes["<row id>"]` in that file. (This is the only way to get
   the hash; it binds the type and every local definition it uses.)
4. Independent review: spawn a separate agent/subagent that did not write the
   proof. Give it only the source excerpt (and the source files for context),
   the Lean statement with the proof replaced by `sorry`, and the definition
   modules it refers to. Ask for a verdict on fidelity: same domain, same
   quantifiers, same hypotheses, same conclusion; whether the Lean is stronger
   or weaker anywhere. Save what it saw next to the review
   (work/reviews/lem-shift-reviewer-input-statement.lean.txt is the example).
5. Write work/reviews/<row>.json with, at least:
   `id`, `reviewer` (identity; say it is an AI reviewer), `statement_sha256`
   (from step 3), `source_sha256` (sha256 of the reference file named in the
   row's `source`), `verdict: "faithful"`, `reason` (the substantive
   comparison), `parameters_reviewed: true`,
   `definition_equivalence_reviewed: true`, `reviewed_files_sha256` (the Lean
   files the reviewer read, with hashes). work/reviews/lem-shift.json is a
   complete example. Verdict not faithful: fix the statement, go to step 3.
6. Set the row: `status: "accepted"`, `author` (implementer identity),
   `reviewer` (must equal the review file's and differ from author),
   `statement_sha256`, `review_file: "reviews/<row>.json"`,
   `parameters_reviewed: true`, `definition_equivalence_reviewed: true`.
   Keep `labels`, `source`, `line` as they are.
7. Run `python3 tools/check_lean.py work/lean` again (the receipt now binds
   the new module) and `python3 tools/progress.py --once`; relay its line.
8. Checkpoint: append to work/AUTHOR_NOTES.md what was decided, update
   work/STATUS.md (state, next unit) and work/TASKS.json. Then the next unit.

A stage check (`--stage 1` / `--all`) additionally requires every row of the
package to be accepted with all of the above consistent; run it only at the end.
