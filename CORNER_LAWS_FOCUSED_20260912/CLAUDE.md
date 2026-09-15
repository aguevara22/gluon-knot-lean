# Instructions for the executor of this folder (read first)

You are the execution lead of a Lean 4 formalization that is already 15% done
(20 of 132 claims verified). Nobody is reachable: no author, no previous
executor, no reviewer, no operator. Do not ask questions of anyone; decide
locally and record the decision in work/AUTHOR_NOTES.md. Read, in this order:
START_HERE.md, STATE_OF_WORK.md, SM15_REALIGNMENT.md, AGENTS.md,
AUTONOMOUS_EXECUTION.md, OPEN_WORK.md, PROOF_PLAN.md, then work/STATUS.md.

Rules that override everything else in this folder:

1. **Assume nothing is installed.** Run `bash setup.sh` first (SETUP.md): it
   installs git, python, the Lean toolchain manager, the pinned toolchain, the
   libraries, then builds and verifies. If it stops, fix what it reports and
   re-run it; never assume a tool, a version or a network path exists. It must
   end with "checker passed: True | mapped 40 | audited 4271". If your command
   runner has a time limit, run it as `nohup bash setup.sh > work/setup.log 2>&1 &`
   and poll the log. Every new shell needs `export PATH="$HOME/.elan/bin:$PATH"`.
2. **Start from the existing work.** work/lean holds 328 compiling modules with
   40 accepted rows and zero sorry. Never delete, rename or rewrite an accepted
   declaration; extend the library.
3. **No sorry, ever, in work/lean.** Scratch attempts live in work/drafts/ and
   are finished or deleted. The checker rejects sorryAx and unregistered axioms.
4. **No questions.** Ambiguity is resolved under AUTONOMOUS_EXECUTION.md with a
   note in work/AUTHOR_NOTES.md. A statement believed false gets an exact,
   kernel-checked counterexample under work/repairs/ and stays unaccepted; the
   work continues on every independent claim.
5. **Claim by claim.** `python3 tools/claims.py --next` recommends the next
   unit (definition or claim) in document order; `--pending-only` lists them
   all. ACCEPT_CYCLE.md is the exact procedure with a worked example: transcribe
   the statement, prove it, obtain independent review, set the row `accepted`,
   re-run the checker, report, checkpoint. GLOSSARY.md maps source notation to
   Lean names. Before writing a proof from scratch, search work/checks for an
   existing candidate body for that row (STATE_OF_WORK.md section 3): the
   previous executor's kernel-checked drafts are to be reused, not redone. Do not accumulate unaccepted candidate declarations;
   the previous executor produced ~2,700 of them in its last day and verified
   no new claim.
6. **Report every 15 minutes while active**: run
   `nohup python3 tools/progress.py --watch > work/progress-watch.log 2>&1 &`
   once per session (a foreground watcher does not survive a tool time limit)
   and relay its newest line in your output channel every 15 minutes:
   `claims verified X/132`; 15 minutes is the maximum gap, report sooner when a
   step ends. Also run `python3 tools/progress.py --once` at startup, at every
   checkpoint and on exit, and relay that line.
7. **Independent review** means a separate agent or session that did not write
   the statement (for Claude Code: a subagent given the source text and the
   Lean type, nothing else). Disclose AI reviews in the review file.
8. **Sources are frozen** (reference/, provenance/, blueprint/). Frame SM15.
   Never edit them; a defect is a counterexample plus a note, not a patch. The
   literature behind the five admitted interfaces is in SOURCES/ (LITERATURE.md
   says what is on file and what is not); the interfaces are stated verbatim
   from blueprint/AXIOM_REGISTRY.md and need no further source to be declared.
9. **Finish**: `python3 tools/check_lean.py work/lean --all` passes,
   FINAL_REVIEW.md is complete, work/delivery/ is packaged. An incomplete stage
   is reported as incomplete, never as done.

Machine: Linux or macOS, 8 cores, 16 GB RAM minimum (32 recommended), 20 GB
free disk, network to github.com and Mathlib's cache. setup.sh installs the rest.
