You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you are
reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row against its printed source:
R:cv_theorem (row 178; the R lane's theorem, FIXED name `RProof.cv_R` and FIXED statement `CV.hyp_R` — the R6 all-parameters
form of the CV campaign's declared input ax:R), module RProof/CvR.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. Printed sources, verbatim: work/reviews/r-cv-theorem-source-excerpt-d10_axioms-lines-15-40.tex.txt (= reference/R/CV/
   d10_axioms.tex 15-40: Axiom "Hypothesis R for X₁" ax:R — X₁(P₊) = X₁(P₋) across every simple Reidemeister III event, i.e. every
   event whose zero set is the forced bundle Z = {G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}} for three pairwise remote edges
   1 ≤ e < f < g ≤ n, concurrent at t = 0 at a point interior to all three, transversal in the sense of def:event), read with
   R_ASSEMBLY_SPEC.md and EXECUTION.json at the handoff root (the R assembly: what the R theorem asserts and from which rows), and
   for notation the CV definitions in reference/R/CV/ (def:event, def:X1, the forced bundle G3/G4).
2. The Lean statement: work/reviews/r-cv-theorem-reviewer-input-statement.lean.txt (RProof/CvR.lean with the proof replaced by
   sorry) and the definition of `CV.hyp_R` in work/lean/RProof/X1Rows.lean (line ~124, namespace CV; its docstring and the definitions it uses: CV.Event,
   IsSimpleRIII, the X1 state sum X1 / X1Summand on the two sides).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/ (Events, Cores, X1, ChamberInvII,
   Axioms), work/lean/RProof/RALedgers.lean (cv_R_of_rows — statement only), the accepted R rows' modules (statements only).
4. Disclosed readings: work/AUTHOR_NOTES.md entries "CV/R tail … design panel judged" (D-CVT-1..6, FR-R-178-1/2) and the row 178
   acceptance entry.

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing RProof.CvR if you
wish): `RProof.cv_R : CV.hyp_R` has no hypothesis; axioms exactly [propext, Classical.choice, Quot.sound, SM.lit_homfly,
SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact] — all registered.

YOUR TASK. Compare `CV.hyp_R` (expanded to primitives) with the printed ax:R: every simple RIII event (the forced-bundle zero set,
the index order e < f < g, pairwise remoteness, interior concurrency at t = 0, transversality per def:event), the two sides P₊ / P₋
and the equality of the X₁ state sums; is anything STRONGER or WEAKER (quantification over events, the all-parameters reading R6 of
R_ASSEMBLY_SPEC, the state-sum definition); label non-blocking notes. Default to "not faithful" if in doubt. The proof route (the
four R rows through cv_R_of_rows) is NOT under review — only the statement.
