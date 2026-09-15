# Prove the corner state sum satisfies the wall laws and soft theorem

This is the only goal. Deliver `SM.corner_laws_and_soft`, on the exact source
domains, with R proved and discharged. The source frame is SM15 (frozen
2026-09-12); ERRATUM_20260912.md and CHANGES_SINCE_20260909.md list what changed
from the SM12 frame of the 2026-09-10 package. Read TARGETS.md for the statements and
PROOF_PLAN.md for the steps. Do not execute the full-SM handoff's other stages.

The author is unavailable. Make routine decisions locally under AGENTS.md and
AUTONOMOUS_EXECUTION.md. Known mathematical work is assigned in OPEN_WORK.md.
The recipient can start by following START_HERE.md and its copyable instruction.

This folder is a RESUMED formalization (see START_HERE.md and STATE_OF_WORK.md):
work/ already holds 327 compiling modules, 39 accepted rows and 19 verified claims.

```sh
bash setup.sh                        # installs Lean and everything else, builds, verifies
export PATH="$HOME/.elan/bin:$PATH"
python3 tools/claims.py --pending-only
python3 tools/progress.py --once
```

Then execute PROOF_PLAN.md in `work/lean`; setup is in `lean/ENVIRONMENT.md`.
Report claims verified/total claims every **15 minutes while running**, and at each
checkpoint. PROGRESS.md supplies the automatic terminal/file reporter and
command wrapper. Start or resume that reporter with each execution session.

There are exactly five permitted literature interfaces in
`blueprint/AXIOM_REGISTRY.md`; R and all CV interfaces require proofs. The
dependency worklist is `blueprint/NODES.tsv`, with `blueprint/ORDER.md` and
`blueprint/DEPENDENCIES.json`. Exact statements and printed proofs are in
`blueprint/STATEMENTS_AND_PROOFS.md`; context is in `reference/`.

Completion requires independent statement review and:

```sh
python3 tools/check_lean.py work/lean --all
```

Here --all checks the single complete focused stage, including R and the final
theorem. --stage 1 is equivalent. Complete FINAL_REVIEW.md as well.
This bundle contains source material and a tested scaffold, not completed proofs.
