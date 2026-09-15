You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912
GENERAL RULES: read only the files listed; expand every local Lean definition to accepted
primitives; compare hypotheses, quantifiers, conclusions and definitions clause by clause; say
where the Lean is STRONGER or WEAKER than the source; any printed sub-clause without a Lean
counterpart is a discrepancy; default to "not faithful" if in doubt. Do NOT open the proof module
named below. OUTPUT: return ONLY a JSON object with keys "verdict" ("faithful" | "not faithful"),
"reason" (clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).

ROW def:star. Source: work/reviews/def-star-source-excerpt-lines-5-14.tex.txt (= reference/SM/sm-5-transport.tex
5-14). Notation: sm-1-polygons.tex def:polygon (labels in Z/n, source label n ≡ 0), def:shift (~398,
reversal P̄_i = μ_{2−i}). Statement: work/reviews/def-star-reviewer-input-statement.lean.txt (main
declaration SM.star_definition). Definition modules: work/lean/SM/StarPolygons.lean (unitPoint, star,
starNeg, definitions only), work/lean/SM/BowTie.lean (bowTie), Reversal (reversal), Polygon. Do NOT open
work/lean/SM/StarDefinition.lean. TASK: for r ≥ 1, N = 2r+1: is u_k = (cos 2πk/N, sin 2πk/N) for k : ZMod N
(via k.val) the printed u_k; is K_r t = u_{r(t−1)} with the source label t ∈ {1..N} read as the residue
t (N ≡ 0) faithful to "K_r = (μ_1, …, μ_N), μ_t = u_{r(t−1)}"; is K_{−r} = reversal K_r the printed
"K_{−r} = \overline{K_r}"; is the bow-tie K_0 = ((0,0),(2,2),(0,2),(2,0)) at labels 1,2,3,4 (4 ≡ 0 in
ZMod 4)? Anything missing (r ≥ 1 restriction), vacuous, stronger or weaker?