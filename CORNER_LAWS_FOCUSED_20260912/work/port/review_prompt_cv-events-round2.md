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

SECOND ROUND (2026-09-13, after an independent first-round review of rows CV:def:interlace, CV:def:event
and CV:def:silent; CV:lem:guardconst is already accepted and is NOT under review now). The module was
revised; the reviewer input file above is the revised module. What changed and what you must judge:

* CV:def:interlace. The first round objected that (i) `CV.U` / the bundle field `mem_U` and the bundle field
  `generic_agree` (agreement with the SM notions) were Lean clauses without a printed counterpart in
  d1_setup.tex 346-353, and (ii) the printed "vertex set [m] = {1,…,m}, m the number of double points"
  (d1_setup.tex 306-308, 347) was rendered only by the tautology `vertex_count` with no clause linking
  `Crossing P` (remote edge pairs whose closed segments meet) to CV's double points `selfIntersections P`.
  Revision: `mem_U` and `generic_agree` were REMOVED from `InterlaceData`; `CV.U`, `CV.mem_U`,
  `CV.U_eq_generic` and the new standalone theorem `CV.interlace_generic_agree` remain in the module as
  ordinary (non-row) theorems — confirm they are outside the bundle. Two fields were ADDED: `vertices`
  (for a diagrammatic polygon with 3 ≤ n, `crossingPoint` is a bijection from `Crossing P` onto
  `selfIntersections P`) and `vertex_ncard` (the number of double points equals the number of
  crossings). Judge: does the bundle now pin down the printed vertex set exactly (the printed row speaks
  of a diagrammatic polygon; the bundle is stated for `CrossingGeometry P` and the two new fields carry
  the hypotheses `Diagrammatic P` and `3 ≤ n` — is that the printed domain for this clause)? Are the
  remaining fields (`occurrences`, `vertex_count`, adjacency = the two occurrences alternate /
  "exactly one" between-clause, `irrefl`, `Ind`, `N`) exactly the printed clauses, with `occurrences`
  rendering the subsection preamble d1_setup.tex 306-313 that the printed clause "the Gauss word" refers
  to? Decision F2 stands: no narrowing to SM's locus.
* CV:def:event. The first round objected that the printed tangency example (d1_setup.tex 1088-1096: path
  p1=(0,0), p2(t)=(2,−t²), p3=(1,0), p4=(3,2); generic for t ≠ 0; zero set = the cusp bundle at t = 0;
  P(t) = P(−t); the two punctured sides lie in the same chamber; no crossing is created) had no
  counterpart in `EventData`. Revision: a new section `TangencyExample` defines `tangencyPath` and
  `tangencyExample : Event 4` (radius 1; indices from 0, so the printed p1..p4 are indices 0..3) and a
  companion bundle `EventExampleData` (fields curve_eq, radius, generic_punctured, nongeneric_center,
  zeroSet_eq, even, sideChamber_eq, not_signChanges, not_transversal, no_crossing), wired into
  `EventData` as the field `tangency_example`. The zero set is stated EXPLICITLY as
  {G1_1, G2_{0,2}, G2_{1,0}} (the turn at the moving vertex and the two G2 members putting p_2 = (1,0) on
  the line of e_0 and p_0 = (0,0) on the line of e_1) because "the cusp zero bundle" is defined in a
  later CV row (not in this row's source): judge whether that explicit set is what the printed text
  means by the cusp bundle at t = 0 for this path (a kink at the moving vertex: p0, p1(0), p2 collinear
  with p1(0) = (2,0) outside the segment [p0, p2]), and whether "no crossing is created" is rendered
  exactly by `¬ Crosses (tangencyPath t) e f` for every t and `crossingSet (tangencyPath t) = ∅` for
  t ≠ 0 (note: at t = 0 the closed segments e_0 = [(0,0),(2,0)] and e_2 = [(1,0),(3,2)] share the vertex
  p_2, so SM's closed-segment `IsCrossing` holds there while CV's activation `Crosses` fails — the
  module documents this in `tangencyPath_zero_isCrossing`; say whether the rendering is faithful). The
  first-round items "We say the event is guarded relative to Z …" (terminology) and "Every named event
  of the convention that lists them is required to be transversal" (a requirement on conv:events,
  another row) are recorded by the executor as non-definitional prose with no Lean counterpart; the
  interpretive reading of "changes sign at t = 0" as `Event.SignChanges` (∃ δ ∈ (0, ε], ∀ t ∈ (0, δ),
  φ(P(t))·φ(P(−t)) < 0) is unchanged — say whether you accept these dispositions. Docstring citations
  now say 1072-1097.
* CV:def:silent. The first round objected that the bundle fields `isSimpleRIII_iff` and
  `silent_not_simpleRIII` rendered CV ax:R (d10_axioms.tex 18-24), not the printed def:silent
  (d1_setup.tex 1265-1271). Revision: both fields were REMOVED from `SilentData`; `Event.IsSimpleRIII`
  stays as a definition for the later ax:R rows and `Silent.not_isSimpleRIII` as a standalone theorem
  (neither is part of the row). Confirm the bundle (silent_iff, g2_vanishing_iff_line,
  silent_iff_segment, no_turn, no_crossing_order, no_concurrency, no_direction) is exactly the printed
  definition ("every member of Z is a G2_{e,i} whose vanishing at t = 0 places p_i on the LINE of e but
  not on the SEGMENT e"; "in particular no member of Z is a turn (G1), a crossing-order predicate (G4), a
  concurrency (G3) or a direction determinant (G5)"), with `Event.Silent` defined as the printed
  condition on the zero set.

Cite line numbers of the revised reviewer input file. A discrepancy you consider non-blocking must be
labelled "non-blocking" in its text; a verdict "faithful" with unlabelled discrepancies will be read as
blocking.
