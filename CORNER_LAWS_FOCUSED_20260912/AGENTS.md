# Execute this focused handoff (resumed on frame SM15)

- Prove only the corner state sum's wall laws and soft theorem described in
  TARGETS.md. Execute PROOF_PLAN.md from the state in STATE_OF_WORK.md; do not
  restart from zero and do not stop after a plan.
- Nobody is reachable: no author, no previous executor, no reviewer, no
  operator. Never ask a question. Decide setup, notation, module layout, helper
  proofs and repairs locally; record nonblocking notes in work/AUTHOR_NOTES.md.
- Mathematical statements in reference/ (frame SM15) are authoritative. Keep
  reference/, provenance/, blueprint/ and the Lean template unchanged;
  implement in work/. Never edit an accepted declaration.
- No sorry in work/lean, ever; scratch goes to work/drafts/. Never add an axiom,
  conceal a gap, strengthen a premise or change a source target to make a
  proof pass. A suspected false statement gets an exact kernel-checked
  counterexample under work/repairs/ and stays unaccepted.
- Work claim by claim in the order of `python3 tools/claims.py`: transcribe,
  prove, independent review, accept, checkpoint, report. Do not accumulate
  unaccepted candidate declarations.
- Obtain independent statement review from another qualified agent or session
  with no authorship of the statement; disclose AI reviews. Review pending
  means incomplete, not blocked from doing further proof work.
- Follow PROGRESS.md: report claims verified/total claims at startup, each
  checkpoint, every fifteen minutes while active, and on exit. Run the
  automatic reporter during long commands and relay reports in the execution
  channel.
- Keep updates concise. Justify nontrivial proof steps. Mark uncertainty explicitly.
