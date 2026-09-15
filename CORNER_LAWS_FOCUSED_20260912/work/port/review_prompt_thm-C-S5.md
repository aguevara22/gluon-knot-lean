You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/thm-C-S5-source-excerpt-lines-910-913.tex.txt (= reference/SM/
   sm-4-knotlaws.tex 910-913, thm:C-S5: "At a simple empty cusp, C(P_no) = 0."). Context, ONLY to fix notation:
   reference/SM/sm-4-knotlaws.tex 914-983 (its printed proof: cases A/B, corners c₁, c₂, lem:cusp-sides (ii),(iii)),
   reference/SM/sm-1-polygons.tex 737-762 (def:walls: type (K) cusp at j — Z_pt, Z_c, μ_j outside the closed segment,
   τ_j changes sign; the newborn pair; the LOOP side (where the newborn pair is a crossing) and the NO-LOOP side;
   "the cusp is empty if on the loop side the two visits of the newborn crossing are cyclically adjacent in the
   Gauss word"), 1051-1100 (lem:cusp-sides: cases A/B, (f,g), (c₁,c₂), loop/no-loop sides), and def:germ (grep
   `label{def:germ}`), reference/SM/sm-3-statesum.tex 1688-1700 (def:C).
2. The Lean statement with the proof replaced by `sorry`: work/reviews/thm-C-S5-reviewer-input-statement.lean.txt
   (definition `WallGerm.EmptyCusp`, bundle `CS5Data`, main declaration `SM.thm_C_S5`). Its module docstring maps
   notation — verify, do not trust. Do NOT open work/lean/SM/CS5.lean.
3. Lean definition modules (definitions and docstrings; the accepted rows def:germ, def:walls, lem:cusp-sides,
   def:gauss, def:C): work/lean/SM/CuspDefinition.lean (CuspCase, CuspAt, cuspFirst, cuspLast, cuspCorner₁/₂),
   CuspSideCrossings.lean (cuspLoopSide, cusp_loop_crossing — statement), CuspSides.lean (CuspSidesData — the
   accepted lem:cusp-sides bundle; read its `empty_middle_edge` hypothesis form), WallGerm.lean / GermDefinition.lean
   (WallGerm, Parameter, SideParameter, sideTuple, sideTime, center, pointZeros, concurrences, SignChanges),
   GaussCyclicGap.lean (GaussVisitsAdjacent), ThreeEdgeCrossingArc.lean (twoStepFirstVisit, twoStepLastVisit),
   GaussVisits.lean (Visit, nextGaussVisit — accepted def:gauss), CornerStateSum.lean (cornerStateSum — def:C).

YOUR TASK: decide whether the definition + bundle pin down exactly the printed theorem. (a) "a simple empty cusp":
`g : WallGerm n` with `h : g.CuspAt j` (is CuspAt exactly def:walls (K)?), its case `b` with `hc : CuspCase g.center
j b` (is quantifying over b with hc the same as the printed "exactly one case applies"?), and `g.EmptyCusp h hc` —
"on the loop side the two visits of the newborn crossing are cyclically adjacent in the Gauss word" rendered as:
for EVERY loop-side parameter s, GaussVisitsAdjacent of twoStepFirstVisit/twoStepLastVisit of the newborn crossing
`{cuspFirst b j, cuspLast b j}` (is ∀ s the right reading of "on the loop side"? are those two visits the two visits
of the newborn crossing? is GaussVisitsAdjacent = cyclically adjacent in the Gauss word of def:gauss?); (b)
"C(P_no) = 0": `cornerStateSum … (g.sideTuple (!(g.cuspLoopSide b j)) t).property = 0` for every no-loop-side
parameter t (is `!(g.cuspLoopSide b j)` the printed no-loop side? is quantifying over all t the printed P_no —
the printed proof says "choose a generic polygon P sufficiently near the wall on its no-loop side" and closes with
constancy on the chamber; is "for every t in the germ's side interval" faithful or stronger?); (c) the standing
assumptions (n ≥ 4 inside CuspAt; NeZero n). Expand definitions to primitives; say where the Lean is STRONGER or
WEAKER; default to "not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
