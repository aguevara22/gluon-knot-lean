You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE definition row of the CV lane against ONE printed source definition of the
paper "CV" (reference/R/CV/d1_setup.tex, frozen). The row is named in your task.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: CV:def:smoothing → work/reviews/cv-def-smoothing-source-excerpt-lines-355-361.tex.txt
   (= d1_setup.tex 355-361); CV:def:wind → work/reviews/cv-def-wind-source-excerpt-lines-487-513.tex.txt (487-513);
   CV:def:pieces → work/reviews/cv-def-pieces-source-excerpt-lines-514-521.tex.txt (514-521). Context, ONLY to fix
   notation: the other two excerpts; d1_setup.tex 315-344 (def:diagrammatic), 220-238 (def:generic), 346-353
   (def:interlace: Ind, N, U), 362-486 (lem:carriers and lem:carrierword — the carriers of a support, only for the
   vocabulary "carrier", "corner", "smoothing site"), reference/SM/sm-1-polygons.tex 240-300 (SM def:gauss / def:interlace)
   and reference/SM/sm-3-statesum.tex 100-200 (SM def:decomposition / def:smoothing / conv:selected-visits — the SM
   rendering of the same operations, accepted). You MAY read the executor's recorded CV-DOM decision in
   work/AUTHOR_NOTES.md (entry "CV-DOM decided: F2 mechanism = (C) on the accepted geo layer" of 2026-09-14): the CV
   rows are stated on their PRINTED binders (hD : CV.Diagrammatic P for def:smoothing and def:pieces; hG : CV.Generic P
   for def:wind), the carriers being the accepted SM.GeoCarrier objects of def:flat-carriers read through
   hD.crossingGeometry / hG.crossingGeometry; the ownership of the two visits of a selected crossing follows SM
   conv:selected-visits (the same selectedMarkPerm), a disambiguation the CV text leaves implicit.
2. The Lean statements with the three row proofs replaced by `sorry`: work/reviews/cv-carriers-reviewer-input-statement.lean.txt
   (module CV/Carriers.lean: module docstring with the notation map — verify, do not trust; the auxiliary definitions
   (weight, wind, CarrierUniform, CarrierMixed, residualGraph, Piece, pieceOf, pieceLabels, …) ARE under review as part
   of the rows; the bundles SmoothingDefinitionData / WindDefinitionData / PiecesDefinitionData with one field per
   printed clause; theorems CV.smoothing_definition, CV.wind_definition, CV.pieces_definition). Helper lemmas' proofs
   are not under review. Do NOT open work/lean/CV/Carriers.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/FlatCarriersDefs.lean
   (the accepted def:flat-carriers geo layer: geoMarkPosition, geoMarkSuccessor, geoSmoothingSuccessor (the reconnection
   at selected crossings), GeoComponent, geoOwner, geoComponentMarkList, geoComponentCornerList, geoCornerCount,
   geoCornerMark, geoCornerPolygon, geoCornerTurn, geoInEdge, geoOutSlot, geoSmoothingSegment, geoComponentPlaneCycle,
   geoCarrierCrossings, GeoIndependent, geoCarrierSelector — definitions and docstrings), SM/CrossingGeometry.lean
   (CrossingGeometry), SM/GeoCarrierGeometry.lean (SM.CarrierGeometry), CV/CarrierBridges.lean (ofDiagrammatic, ofCV,
   mem_Ind_iff_geoIndependent, mem_N_iff, mem_U_iff), CV/Setup.lean (CV.Diagrammatic, CV.Generic, guards G1..G5),
   CV/Events.lean (CV.Ind, CV.N, CV.U — accepted CV:def:interlace), SM/GeometricInterlacement.lean
   (geometricInterlacementGraph, GeometricInterlaces), SM/Chirotope.lean (turn), SM/Crossings.lean (crossingSign,
   crossingPoint, visitTwin), SM/Polygon.lean (edge, edgeSegment), SM/Traversal.lean (traversalEvaluation).

YOUR TASK: for YOUR row only, decide whether the definitions + bundle render exactly the printed definition on its
printed binder. def:smoothing (d1:355-361) — read the printed text and check each field: the reconnection at selected
crossings (reconnect_selected: successor swap between the two visits; keep_unselected; keep_vertex), transverse
(the smoothing site is a transverse crossing point), oriented_arcs / inherited_direction (the new arcs are positive
multiples of the parent edge directions), noncrossing_arcs (the two new arcs do not cross — rendered as opposite
nonzero turning signs: is that the printed "do not cross"?), carriers = cycles of the smoothing successor,
closed_oriented, disjoint_union, traced_curve, straight_pieces. def:wind (d1:487-513) — binder hG : CV.Generic P
("Let P be generic and S ∈ Ind(G_P) — the binders under which the definition is read"); corners (corner_iff: vertex or
smoothing site traversed), turn signs (turn_sign = sign det(in, out); turn_ne_zero; vertex_corner via (G1); smoothing_corner
via (G5)), the printed counterexample "((0,0),(1,0),(2,0),(0,1)) is diagrammatic and its turn at p₂ is exactly zero"
(not_decoration — is a formalised counterexample a faithful rendering of that sentence or an addition?), uniform / mixed,
the weight table (weight_right = +1, weight_left = (−1)^{c(L)} with c(L) = #corners = geoCornerCount, weight_mixed = 0),
wind = ∏ over the |S|+1 carriers, "wind(S) ≠ 0 forces every carrier uniform". def:pieces (d1:514-521) — U(S) = [m] ∖
(S ∪ N(S)) (undominated, undominated_eq, neighbors), the residual pieces = connected components of the induced subgraph
G_P[U(S)] (residualGraph = induce, Piece = ConnectedComponent, pieceOf, pieceLabels, the partition clauses). Expand
definitions to primitives; say where the Lean is STRONGER or WEAKER; any printed clause without a Lean counterpart or
Lean field without a printed counterpart is a discrepancy; default to "not faithful" if in doubt; label non-blocking
discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
