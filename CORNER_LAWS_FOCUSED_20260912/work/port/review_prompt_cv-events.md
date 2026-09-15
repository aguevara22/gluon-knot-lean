You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row of the CV lane against ONE printed source statement of the
paper "CV" (reference/R/CV/d1_setup.tex, frozen). The row is named in your task.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim, for your row (the file name gives the d1_setup.tex lines):
   CV:def:interlace → work/reviews/cv-interlace-source-excerpt-lines-346-353.tex.txt;
   CV:def:event → the file work/reviews/cv-event-source-excerpt-lines-1072-*.tex.txt;
   CV:lem:guardconst → work/reviews/cv-guardconst-source-excerpt-lines-1107-*.tex.txt;
   CV:def:silent → work/reviews/cv-silent-source-excerpt-lines-1265-*.tex.txt.
   Context, read ONLY to fix notation: the other three excerpts, the five excerpts of the CV
   definition rows the module builds on (work/reviews/cv-def-{polygon,regular,guarded,generic,
   diagrammatic}-source-excerpt-*.tex.txt = d1_setup.tex 8-19, 22-40, 42-218, 220-238, 315-344),
   reference/R/CV/d1_setup.tex 239-314 (remarks between generic and diagrammatic) and 1122-1264 (the
   text between guardconst and silent, only where a definition you need is introduced), and — for
   the SM notions the interlace row relates to — reference/SM/sm-1-polygons.tex 240-268 (SM
   def:gauss, def:interlace: visits, alternation, interlacement, N(S), U(S)).
2. The Lean statement with the row proofs replaced by `sorry`:
   work/reviews/cv-events-reviewer-input-statement.lean.txt — the whole module CV/Events.lean with
   the four row theorems (CV.interlace_definition, CV.event_definition, CV.guardconst,
   CV.silent_definition) replaced by sorry; definitions and helper lemmas (proofs not under review)
   are in this file. Do NOT open work/lean/CV/Events.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/Setup.lean
   (CV.IsPolygon, rep, lineForm, G1..G5, Crosses, Member and Member.eval/Unconditional/Conditional/
   Active/Relevant, Generic, genericLocus, chamber — the accepted-candidate CV definitions of the
   sibling rows), and under work/lean/SM/: GeometricInterlacement and InterlaceCount
   (geometricInterlacementGraph, geometricInterlaces, geometricVisitPosition, geometricCrossingVisitBetween
   — definitions only), CrossingGeometry (CrossingGeometry), Interlacement and InterlaceSupports
   (Interlaces, independentSupports, supportNeighbors, supportUnselected; accepted rows def:interlace
   / def:decomposition), Generic, Polygon, GenericTopology (statements only), EuclideanPlane.

YOUR TASK: for YOUR row only, decide whether the Lean definitions/statement, as pinned down by the
row bundle (or the theorem statement for lem:guardconst), render exactly the printed text. Read the
printed text clause by clause and find the rendering of each clause. Specifics: def:interlace — the
interlacement graph on the crossings of a diagrammatic polygon (vertices = crossings, edges =
interlaced pairs: the visits alternate along the traversal circle), the independent sets Ind, the
neighbourhood N(S) and the unselected set U(S); the Lean states it for a polygon with
`CrossingGeometry` (the accepted geometric Gauss data) — is that the printed domain "diagrammatic"
(row 133 proves Diagrammatic → CrossingGeometry) or wider, and is a wider domain harmless; the
recorded agreement with the SM notions on SM-generic polygons. def:event — "a continuous path
t ↦ P(t) of polygons on n vertices" on a parameter interval, generic off the centre and not generic
at the centre; the zero set (the guards vanishing at the centre), side chambers, "changes sign",
"transversal"; the added field `center_polygon` (the centre is a polygon: nonzero edge directions)
— printed or an addition? def:silent — the silent events and the simple RIII events as printed.
lem:guardconst — the guards outside the zero set: for a member relevant somewhere off the centre
and not in the zero set, its value at the centre is nonzero and it has constant sign on a
neighbourhood; check the exact hypotheses (relevant at SOME off-centre parameter versus at all;
`ε' ≤ E.radius`) and the conclusion against the printed sentences. Decision F2 of the executor: CV
notions are stated on CV's own locus, never narrowed to SM's; flag any narrowing as a discrepancy.
Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; any printed clause
without a Lean counterpart, or any Lean field without a printed counterpart, is a discrepancy.
Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
