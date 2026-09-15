You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/lem-C-X1-source-excerpt-lines-1787-1798.tex.txt (= reference/SM/
   sm-3-statesum.tex 1787-1798, lem:C-X1). Context, read ONLY to fix notation: reference/SM/sm-3-statesum.tex
   1799-1811 (its printed proof), 1688-1700 (def:C: c(Q), C(P)), 242-260 (def:uniform: carriers, corners,
   turns, uniform/mixed), 9-60 (def:decomposition, def:smoothing, lem:carriers: carriers L of an independent
   support S, their corners); reference/SM/sm-1-polygons.tex 63-72 (def:chirotope: turn signs, left turn
   τ_i = 1, ℓ(P)), 240-268 (Ind(G_P)).
2. The Lean statement with the proof replaced by `sorry`: work/reviews/lem-C-X1-reviewer-input-statement.lean.txt
   (definitions `carrierWeight`, `wind`; bundle `CX1Data`; main declaration `SM.C_X1`). Its module docstring maps
   notation — verify it, do not trust it. Do NOT open work/lean/SM/CX1.lean.
3. The def:C definitions the row builds on: work/reviews/def-C-reviewer-input-statement.lean.txt (module
   SM/CornerStateSum.lean with its row proof removed: cornerSlot, cornerCoefficient, cornerProduct,
   uniformDecompositions, cornerStateSum — under separate review as row def:C; judge only whether THIS row uses
   them as the printed lemma uses c(L) and C(P)). Lean definition modules (definitions and docstrings only):
   work/lean/SM/UniformDefinition.lean (CarrierUniform, CarrierMixed, UniformDecomposition, carrierLeftTurns),
   CarrierCornerPolygon.lean (ccpCornerCount = k(L), ccpCornerPolygon, ccpCornerMark; statements of
   ccpCornerPolygon_turn_ne_zero / _turn_vertex / _turn_smoothing), CarrierSmoothing.lean (Component = the
   carriers L of S), InterlaceSupports.lean (independentSupports = Ind(G_P)), DecompositionDefinition.lean,
   Chirotope.lean (turn, leftTurns).

YOUR TASK: decide whether the definitions + bundle pin down exactly the printed lemma. Check: (a) "For a
carrier L of an independent support S, let k(L) be its number of corners" — `q : Component hn hP S`,
`ccpCornerCount hn hP S q`; (b) "wt(L) = 1 if all its turns are right, (−1)^{k(L)} if all are left, and 0 if
its turns are mixed" — `carrierWeight` with turns `turn (ccpCornerPolygon …) j` (is right = −1 and left = 1
the printed convention? are "all turns right/left/mixed" exhaustive and exclusive given nonzero turns, and is
"mixed" rendered exactly as "neither all right nor all left"?); (c) "wind(S) = ∏_L wt(L)" — `wind`; (d) eq.
C-selector-form "C(P) = Σ_{S ∈ Ind(G_P)} wind(S) ∏_L c(L)" — `selector_form` (sum over
`(independentSupports hn hP).attach`, `cornerProduct` = ∏_L c(L) with c(L) "the coefficient of the actual
positive carrier lift in def:C"); (e) the bundle fields weight_right / weight_left / weight_mixed / wind_eq
as the printed defining clauses. Expand definitions to primitives; say where the Lean is STRONGER or WEAKER;
any printed clause without a Lean counterpart or Lean clause without a printed counterpart is a
discrepancy. Default to "not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
