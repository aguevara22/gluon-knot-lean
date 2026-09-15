# Infrastructure validation — 2026-09-10

- Verified the source subset against all four original pinned manifests and
  checked every extracted statement/proof segment against the unchanged source.
- Verified 59 bridge quotations against SM15 through the pinned realignment
  ledger; no replay of the absent full SM11 frame is claimed.
- Checked that the dependency graph is acyclic, every required node is reachable
  from the final goal and the acceptance map contains 191 unique obligations.
- Bootstrap preserves existing progress and declaration maps on restart.
- The automatic reporter passed startup, short-interval periodic and exit tests,
  including a nonzero child exit. Scope persists across restarts; deleted pending
  rows, malformed state and duplicate IDs do not create false progress.
- Logging write failures do not prevent the execution command from running.
- A complete synthetic acceptance cycle passed. Changed/missing reviews, changed
  local helper meanings, new project files and source changes invalidated the
  receipt. Editing the working audit module was rejected.
- A temporary core-only project on the exact Lean pin built successfully.
  Empty formalization was rejected by focused stage 1, stage 2 was rejected as
  outside scope, and the excluded sixth literature axiom was rejected.

Reproduce subset checks with `python3 verify_bundle.py` and reporter tests with
`python3 tools/selftest_progress.py`. The shared full-handoff checker also passed
its sorryAx, unused-axiom and native_decide rejection tests. The underlying pinned
Mathlib scaffold and a focused Mathlib import were tested in the full handoff;
the temporary core-only checks above do not claim a Mathlib theorem-library build.

Frame SM15 realignment (2026-09-12): the source subset now comes from frame SM15;
ERRATUM_20260912.md, CHANGES_SINCE_20260909.md and DIFF_SM12_to_SM15.txt record
what changed from the SM12 frame shipped on 2026-09-10. Statements whose formal
content changed: lem:shift (iii),(iv), lem:g1 (iv), prop:A-chamber, lem:softvertex.

No mathematical formalization, source-fidelity review or R assembly is completed
by these infrastructure checks. Run the recipient's own checks on the actual
implementation and retain the evidence described in lean/ENVIRONMENT.md.
