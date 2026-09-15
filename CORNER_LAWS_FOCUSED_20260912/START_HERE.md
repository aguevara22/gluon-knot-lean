# Start here — resumed formalization, frame SM15 (handover of 2026-09-12)

This folder is a formalization in progress, not a fresh scaffold: 20 of 132
claims are verified, 40 of 192 checklist rows accepted, 0 of 8 final targets;
328 Lean modules that build with zero sorry. Nothing outside this folder is
needed or reachable. Nobody is available to answer questions.

Nothing is assumed installed. `bash setup.sh` installs git, python, the Lean
toolchain and the libraries, builds, and verifies (SETUP.md explains). Measured
at 5 minutes on a bare 8-core Debian machine; up to an hour on a slow network.

Give the executing agent this folder as its working directory and paste:

> Execute this folder to completion. Read CLAUDE.md and follow it. Nothing is
> installed on this machine: run `bash setup.sh` first (it installs Lean and
> builds the library; if it stops, fix what it reports and re-run it). It must
> end with the checker passed, 40 mapped and 4271 audited declarations. Then
> prove the remaining claims one at a time in the order of
> `python3 tools/claims.py`, with zero sorry and independent review of every
> statement. Run `python3 tools/progress.py --watch` and relay the line
> "claims verified X/132" every 15 minutes while you work. There is nobody to
> ask: decide locally and record decisions in work/AUTHOR_NOTES.md. Finish when
> `python3 tools/check_lean.py work/lean --all` passes and FINAL_REVIEW.md is
> complete.

Literature for the five admitted interfaces: SOURCES/ and LITERATURE.md.

Procedure for one unit of work: ACCEPT_CYCLE.md. Notation: GLOSSARY.md.

Reading order for the agent: CLAUDE.md, SETUP.md, ACCEPT_CYCLE.md, STATE_OF_WORK.md,
SM15_REALIGNMENT.md, AGENTS.md, AUTONOMOUS_EXECUTION.md, OPEN_WORK.md,
PROOF_PLAN.md, work/STATUS.md.

work/checks is the previous executor's candidate lane: 481 kernel-checked but
unaccepted Lean bodies (2,714 theorems) towards the soft theorem of the tree
amplitude and the carrier construction, with prototypes and result receipts. It is
part of the work that was paid for. Its per-checkpoint checker logs and audit dumps
(4 GB; nothing reads them, the checker rewrites the current receipts on every run)
are not in the shipped copy. Before writing any claim from scratch, look there for an existing body
(STATE_OF_WORK.md section 3 lists the main ones) and port it through ACCEPT_CYCLE.md.
