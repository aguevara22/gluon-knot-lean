You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you are
reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE theorem row against ONE printed source
statement (frame SM15): thm:comparison (row 127; FIXED name `SM.thm_comparison`), module SM/ComparisonRows.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/thm-comparison-source-excerpt-lines-299-311.tex.txt (= reference/SM/sm-6-comparison.tex
   299-311, thm:comparison: "Assume Hypothesis R. Then C(P) = A(P) for every generic polygon P", with its printed proof through
   thm:uniqueness (a)-(f)). Context ONLY to fix notation: reference/SM/sm-6-comparison.tex 1-120 (def:weak-amplitude, A_g, cor:A-lawful
   "A(P) := A_g(P) (any g)"), the label thm:uniqueness (grep), reference/SM/sm-4-knotlaws.tex (hyp:R, grep `label{hyp:R}`),
   reference/SM/sm-3-statesum.tex 1688-1700 (def:C).
2. The Lean statement with the proof replaced by `sorry`: work/reviews/thm-comparison-reviewer-input-statement.lean.txt (the row
   declaration `SM.thm_comparison (hR : hyp_R) : ∀ n [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P), cornerStateSum hn hP =
   amplitude P hP.1 hn`). Do NOT open work/lean/SM/ComparisonRows.lean's proofs (the statement file is what you review).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/ALawful.lean:40 (`amplitude`, accepted cor:A-lawful material), work/lean/SM/Comparison.lean (the accepted
   library theorem `thm_comparison_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) : …` — statement and docstring only; `UniquenessHypotheses`,
   `cornerPolygon`), the accepted rows' modules for `amplitude` / `treeCoefficient` / `A_g` (grep `def amplitude`, `def treeCoefficient`
   in work/lean/SM/), SM/HypR.lean (`hyp_R`, accepted), CornerStateSum.lean (`cornerStateSum`), Generic (G1 ∧ G2; grep `def Generic`),
   and the accepted reviews work/reviews/cor-A-lawful.json, work/reviews/hyp-R.json, work/reviews/thm-uniqueness*.json (grep) for the
   readings of A(P) and Hypothesis R.

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing SM.ComparisonRows if you
wish): `SM.thm_comparison` has exactly one hypothesis `hR : SM.hyp_R` (hyp:R in `explicit_parameter` mode, as the printed "Assume
Hypothesis R"); axioms exactly the nine registered [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm,
SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]; no sorryAx. The proof is the one-liner `thm_comparison_of hR thm_C_S7 thm_C_soft`.

YOUR TASK: decide whether the statement pins down exactly the printed theorem: (a) "Assume Hypothesis R" = the explicit parameter `hR :
hyp_R` (is SM.hyp_R the printed hyp:R — every simple triple wall germ, C(P₊) = C(P₋)?); (b) "for every generic polygon P" = ∀ n ≥ 3,
[NeZero n], P : LabelledTuple n, hP : Generic P (is Generic = (G1) ∧ (G2) the printed "generic"? does the statement range over labelled
tuples rather than polygons — is that faithful given C and A are cyclically invariant / defined on labelled tuples in the source?);
(c) "C(P) = A(P)" = `cornerStateSum hn hP = amplitude P hP.1 hn` (is `amplitude P hP.1 hn` the printed A(P) := A_g(P) (any g) of
cor:A-lawful — which root does `amplitude` use, and is root independence accepted?). Expand definitions to primitives; say where the
Lean is STRONGER or WEAKER; default to "not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite source and
statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of strings),
"supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
