You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/lem-carriers-source-excerpt-lines-54-95.tex.txt
   (= reference/SM/sm-3-statesum.tex 54-95, lem:carriers (i)-(iv)); context sm-3 lines 1-52
   (def:decomposition, def:smoothing, conv:selected-visits — all accepted rows) and the proof 96-240
   ONLY to disambiguate notation (in particular the finite successor model ρ, ρ_S at 96-116, which the
   Lean rows adopt as the definition of carriers); sm-1-polygons.tex def:crossings, def:gauss,
   def:interlace (interlacing, N(S), U(S)), def:regular (regular locus), def:chirotope (turns).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/lem-carriers-reviewer-input-statement.lean.txt (main declaration SM.carriers_lemma;
   bundle CarriersLemmaData). Its module docstring maps notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): CarrierMarks, CarrierSuccessor, CarrierVisitTwin, CarrierSmoothing (smoothingSuccessor,
   Component, owner), CarrierFilteredCycles (componentCycle), CarrierInheritedOrder (InheritsMarkOrder),
   CarrierAffineSegments (smoothingSegment), CarrierTrueCorners (IsTrueCorner), CarrierClosedTrace,
   CarrierCrossings (carrierCrossings), CarrierCornerPolygon (ccpCornerList, ccpCornerCount,
   ccpCornerMark, ccpCornerPolygon — definitions only), CarrierSelfIntersections (IsCarrierParameter,
   carrierTrace, IsSelfIntersection, IsTriplePoint — definitions only), CarrierNoncrossing (definitions
   only), SmoothingDefinition / SelectedVisitsConvention / DecompositionDefinition (accepted rows),
   InterlaceSupports (independentSupports, supportNeighbors, supportUnselected), Interlacement, Traversal
   (traversalBetween), GaussVisits (Visit, visitPosition), Crossings (Crossing, crossingPoint,
   crossingSign), RegularLocus (Regular), Chirotope (turn), Polygon (edge, edgeSegment), Generic.
   Do NOT open work/lean/SM/CarriersLemma.lean (it contains the proof).

YOUR TASK: compare the four printed clauses with the bundle fields. (i) "exactly |S|+1 carriers,
independent of the order of reconnections" (count; order-independence is structural: ρ_S is defined
from S alone — say whether that suffices), "each carrier traverses the visits assigned to it in
their cyclic order inherited from the original traversal circle" (component_cycle + inherited_order:
the cycle of q is the owner-filtered marked circle and its successor is ρ_S), "the two visits of a
selected crossing belong to different carriers" (selected_visits_separated). (ii) "every carrier
has nonzero edges, at least three corners, no antiparallel consecutive directions; all corner turns
nonzero; at an original vertex i the turn sign is τ_i; at a selected crossing of E_i, E_j the two
smoothing corners have signs sgn det(d_i,d_j) and sgn det(d_j,d_i), one left and one right"
(corner_polygons: check the corner polygon ccpCornerPolygon is the carrier read at its corners in
inherited order, the trace equality, edges as positive multiples of original directions, Regular,
turn facts, crossingSign = sgn det). (iii) "a carrier's self-intersections are exactly the unselected
crossings both of whose visits are assigned to it; transverse; none is a corner; no triple point;
an unselected crossing interlacing some element of S has its visits on different carriers; one
interlacing no element of S has both visits on one carrier" (self_intersections,
neighbor_visits_separated, nonneighbor_visits_together: check IsSelfIntersection / IsTriplePoint /
carrierTrace parametrise the traced curve faithfully, and what "transverse" and "not a corner" are
encoded as). (iv) "no four distinct visits u₁,u₂,u₃,u₄ in that cyclic order with u₁,u₃ on one carrier
and u₂,u₄ on a different carrier, including selected visits" (noncrossing: check the cyclic-order
encoding via traversalBetween and that selected visits are included). Domain: P generic, n ≥ 3, S an
independent set of crossings (IsDecomposition). Expand definitions to primitives; say where the Lean
is STRONGER or WEAKER; any printed sub-clause without a Lean counterpart is a discrepancy. Default to
"not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
