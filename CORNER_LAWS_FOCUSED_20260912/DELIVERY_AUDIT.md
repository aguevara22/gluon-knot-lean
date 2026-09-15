# Delivery audit — 2026-09-10, revision 2

This audits the handoff packages, not the truth or completion of the commissioned
Lean mathematics. No SM/R/bridge theorem is claimed proved by these checks.

## Defects corrected

1. A receipt previously bound project files but not its review evidence. Deleted
   or rejected review files could therefore leave progress displaying a current
   receipt. Receipts now bind reviews, code, sources and policy, and detect added
   project files as well as changes/deletions. Old-format receipts are not current.
2. A theorem's old review hash did not follow local helper definitions giving its
   type meaning. The hash now includes those transitive definitions and universe
   parameters. Changing a helper invalidates dependent reviews. The working
   project cannot silently replace the supplied audit module.
3. A progress-file write error could stop the execution wrapper before the proof
   command started. Logging errors now remain visible without preventing that
   command from running. Invalid timer intervals are rejected explicitly.

START_HERE.md adds an exact first-run instruction for the recipient.
R_ASSEMBLY_SPEC.md makes the missing fibre-sum assembly precise. FINAL_REVIEW.md
lists the statement/domain checks, and `check_lean.py --all` checks every stage
commissioned by the selected package.

## Requirement/evidence audit

| Requirement | Evidence examined |
|---|---|
| Focused goal is C's wall laws and soft theorem | TARGETS.md contains the selected direct/inherited source statements; FINAL_REVIEW.md covers every branch, full cusp domain and all soft sectors. |
| Only the selected proof route is commissioned | Recomputed the 134-SM/36-CV closure and two clause selections from source; inspected the one excluded historical marked-data reference. The initial map has 191 obligations. This is not a proof of mathematically minimal dependencies. |
| No circular R input or extra literature axiom | Checked the recorded R dependency closure excludes downstream SM comparison/inherited laws and CV campaign axioms. CV ax:R is a proposition to define; R:cv_theorem proves it. The focused allowlist contains five literature interfaces. |
| Extracts are complete and faithful copies | Compared all 277 full statement/proof spans with parser attribution, checked both clause statements and proof endpoints, and matched aliases/environments/actions to source. No cross-file or truncated extraction was found. |
| Source bytes stay unchanged | Original pinned SM12/CV/RA/bridge manifests; all 66 full payloads and the focused 25-file subset; 59 exact quotations with the disclosed SM12 legend relocation. |
| Missing work does not become a question or axiom | Read both policies, OPEN_WORK.md and the concrete R assembly specification. Missing assembly, translation, independent review and full-package census are assigned locally and are not claimed complete. |
| Startup and restart work | Fresh extraction, verification, bootstrap, initial 0% report and repeated bootstrap preserving existing work. |
| Progress is periodic and does not obstruct execution | Startup/periodic/exit tests with short intervals using the same timer path; default interval is 600 seconds. Tested malformed/duplicate state, deleted pending rows, persisted scope, write failure and child exit status. |
| Acceptance can succeed for valid input and reject stale evidence | Complete synthetic core-Lean source/review/acceptance cycle, then changed/missing/rejected reviews, changed helper meaning, changed source and added project files. This is an infrastructure fixture, not a review of the source mathematics. |
| Every full stage is required | Synthetic three-stage --all run; missing Stage-2 certificate is rejected after Stage 1 succeeds. Focused --all commissions its single complete stage. |
| Kernel/axiom checks still work | Pinned Lean controls reject an unused unregistered axiom, sorryAx and native_decide; focused policy rejects the excluded sixth literature axiom. |
| Real Mathlib compatibility | Revised auditor built and checked a focused Mathlib.Data.Nat.Basic proof on the supplied pinned dependency. No full umbrella Mathlib or mathematical-library build is claimed. |
| Archives are usable | Final ZIP entries, SHA-256 sidecars, fresh extracted verification and bootstrap. |

Reproduce portable checks with `verify_bundle.py`, `tools/selftest_progress.py`,
and (in the full package) `tools/selftest_handoff.py --lean`. Both packages supply
`tools/selftest_acceptance.py` for the synthetic acceptance controls.

Independent mathematical fidelity review and actual proofs remain the recipient's
work. In particular, the R aggregate assembly has not been supplied as a Lean
proof. These packages remove identified handoff defects; they do not guarantee
that an unfinished mathematical proof cannot encounter a real obstruction.
