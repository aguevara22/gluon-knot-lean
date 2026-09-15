You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/lc-single-crossing-source-excerpt-lines-1345-1352.tex.txt
   (= reference/SM/sm-3-statesum.tex 1345-1352, lc:single-crossing). Context, read ONLY to fix notation:
   reference/SM/sm-3-statesum.tex 1353-1361 (its printed proof — to understand what "local LM evaluation
   P_D" and "UNDER-first" denote), 1041-1063 (lp:core, where P_D is introduced: "The same source
   construction has an evaluation P_D ∈ R" via the Gaussian substitution l = i a, m = −i z, eq.
   lp:gaussian at 1066-1071), 935-960 (lp:lm: the source function F_D, UNDER-first, initialization
   μ^{c−1}), 325-351 (def:positive-lift: diagrams are the polygonal class).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/lc-single-crossing-reviewer-input-statement.lean.txt (bundle `SingleCrossingData`, main
   declaration `SM.single_crossing`). Its module docstring maps notation — verify it, do not trust it.
3. The DEFINITION of the local polynomial `SM.P` used by the row:
   work/reviews/local-polynomial-definition.lean.txt (= work/lean/SM/LocalPolynomial.lean, definitions and
   docstrings; the sanity theorem's proof is not under review). It defines `P D := reMap (phi (T.toTG (lmF D)))`
   — the coefficientwise REAL PART of the Gaussian evaluation φ(F_D) ∈ R_G = ℤ[i][a^{±1}, z^{±1}] of the
   source value F_D ∈ T. The executor's recorded rationale (work/AUTHOR_NOTES.md entry "lp:coefficient-transport
   proved; the local polynomial P defined", which you MAY read): the printed P_D is φ(F_D), which lp:core
   proves to lie in R ⊂ R_G (integral descent); taking the real part yields an element of R for every
   diagram without presupposing that descent, and lp:core's bundle will record R.toRG (P D) = φ(F_D)
   (imaginary part zero). JUDGE whether this definition of P is a faithful rendering of the printed P_D
   for the purposes of THIS row (whose printed proof computes P_D through F_D = μ^0 = 1 and "the common
   Laurent substitution keeps this value"), and say so explicitly in your verdict reason.
4. Lean definition modules under work/lean/SM/ (definitions and docstrings only): LinkLaurentRing
   (namespace SM.Link: R, T, RG, TG, R.toRG, T.toTG, phi, psi, reMap, imMap, gaussI — definitions), LinkDiagram
   (Diagram, Shadow (c components), Crossing, IsCrossingFreeCircle, componentCount, Basing, basedRank,
   UnderFirst, overVisit/underVisit, IsPositive, sign — definitions), LinkInterfaces (the ACCEPTED lp:lm
   row: LMClauses, lp_lm, lmF, lmF_underFirst_init statement). Do NOT open work/lean/SM/SingleCrossing.lean.

YOUR TASK: decide whether the bundle pins down exactly the printed lemma. Check: (a) "An actual oriented
one-circle diagram" — `D : Diagram` with `D.Γ.c = 1`; (b) "with just one self crossing" — a crossing `x`
with `∀ y : D.Γ.Crossing, y = x` (on one circle every crossing is a self crossing; is the rendering of
"just one" exact?); (c) "has local LM evaluation P_D = 1" — `P D = 1` with `P` as defined above; (d) "for
either crossing sign" — the field carries no hypothesis on `D.IsPositive x` / `D.sign x` (is that the right
rendering of "either"?); (e) "A crossing-free one-circle diagram also has value one" — `D.IsCrossingFreeCircle
→ P D = 1`. Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; any printed clause
without a Lean counterpart or Lean clause without a printed counterpart is a discrepancy. Default to "not
faithful" if in doubt. Label non-blocking discrepancies "non-blocking" in their text.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
