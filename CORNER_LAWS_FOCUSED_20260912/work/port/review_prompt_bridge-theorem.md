You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you are
reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row against its printed source:
Bridge:theorem (row 183; FIXED name `Bridge.sm_R` and FIXED statement `SM.hyp_R`), module Bridge/SmRRow.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. Printed source, verbatim: work/reviews/bridge-theorem-source-excerpt-lines-1443-1475.md.txt (= reference/BRIDGE/BRIDGE.md
   1443-1475, section 3 "The displayed bridge theorem": the frozen RA result in the CV ax:R form implies, for every SM11 simple triple
   wall germ P, C(P₊) = C(P₋) — displays (19)-(21)), read with BRIDGE.md sections 0-1 (the two statements quoted; the RA domain) and,
   for notation, reference/SM/sm-4-knotlaws.tex where hyp:R is printed (grep `hyp:R`) and its accepted Lean rendering SM.hyp_R
   (work/lean/SM/HypR.lean, docstring: the same rendering of "C(P₊) = C(P₋)" as the accepted prop:C-silent).
2. The Lean statement: work/reviews/bridge-theorem-reviewer-input-statement.lean.txt (Bridge/SmRRow.lean with the proof replaced by
   sorry), the definition `SM.hyp_R` (SM/HypR.lean) and the accepted library theorem `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R`
   (Bridge/SmR.lean — statement and docstring only), and `CV.hyp_R` (work/lean/RProof/X1Rows.lean ~124, namespace CV).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/ (WallGerm, TripleAt, SideParameter,
   sideTuple, cornerStateSum — grep), work/lean/Bridge/ (B1-B4, the accepted rows bridge-b1..b4 and their review files
   work/reviews/bridge-b*.json for the identifications), work/lean/CV/.
4. Disclosed readings: work/AUTHOR_NOTES.md entries "CV/R tail … design panel judged" (FR-B-183) and the row 183 acceptance entry.

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing Bridge.SmRRow if
you wish): `Bridge.sm_R : SM.hyp_R` has no hypothesis; axioms exactly the nine registered [propext, Classical.choice, Quot.sound,
SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact].

YOUR TASK. Is `SM.hyp_R` (expanded: ∀ n ≥ 3, every wall germ g with a simple triple wall TripleAt e f k, every pair of side
parameters, cornerStateSum (side true) = cornerStateSum (side false)) exactly the conclusion of the displayed theorem (19)/(21) —
SM11's printed hyp:R "for every simple triple wall germ, C(P₊) = C(P₋)" — and is the row theorem the displayed implication applied
to the proved CV R theorem (the accepted sm_R_of_cv_R being B1-B4)? Is anything STRONGER or WEAKER (the class of germs, the side
parameters, the state sum C); label non-blocking notes. Default to "not faithful" if in doubt. The proof route is NOT under review —
only the statement.
