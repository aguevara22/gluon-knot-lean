---
name: lean-reassessment-rule
description: Mark's automatic reassessment rule for proof work (repos/lean/reassessment_rule.md) — audit after 2 substantive attempts or 60 min without a newly accepted source claim
metadata:
  type: feedback
---

Mark added `/workspace/repos/lean/reassessment_rule.md` on 2026-09-14 ("feel free to use if any branch is stuck, otherwise keep going").
Rule: reassess automatically after two substantive attempts or 60 minutes of active work without a NEW ACCEPTED source claim (helpers,
definitions, compiles, fragment reviews do not reset stagnation; a complete kernel-proved claim whose acceptance is merely delayed → fix
the acceptance bottleneck, don't discard). Trigger immediately on domain mismatch, circularity, impossible interface, repeated failure of
the same method, or growing helper scope without a route to the conclusion. Response: bounded method audit — restate the claim and the
remaining obligation, diagnose (math / representation / decomposition / tools / review / control), compare continue vs change vs abandon,
specify ONE decisive next test with exact target, success criterion, effort bound ≤ next audit window, and consequence on failure; label
unproved feasibility CONJECTURE; record the decision and that the accepted count is unchanged. Resume: read the saved audit state first.

**Why:** Mark wants stalled branches caught and re-planned without his intervention while the accepted-claim count stays honest.
**How to apply:** at each progress report check per-branch stagnation; record audits in work/AUTHOR_NOTES.md ("Stagnation audit" entries);
never weaken claims or reclassify helpers to manufacture progress. See [[lean-project-progress]].
