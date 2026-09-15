You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma row of the CV lane against ONE printed source statement of the
paper "CV" (reference/R/CV/d1_setup.tex, frozen).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-lem-carriers-source-excerpt-lines-362-383.tex.txt (= d1_setup.tex
   362-383, CV:lem:carriers "the carriers of a support": the setup sentence about the traversal circle and the 2m marked
   points, and clauses (i)-(iv)). Context, ONLY to fix notation: d1_setup.tex 384-449 (its printed proof — to see what
   "noncrossing", "in this cyclic order", "lie on one carrier" denote), 355-361 (def:smoothing), 315-344
   (def:diagrammatic), 346-353 (def:interlace: Ind, N, U), 514-521 (def:pieces). You MAY read the executor's CV-DOM
   decision in work/AUTHOR_NOTES.md (entry "CV-DOM decided: F2 mechanism = (C) on the accepted geo layer" of 2026-09-14:
   printed binders; carriers = the accepted SM.GeoCarrier objects through hD.crossingGeometry; the ownership convention at
   a selected crossing is SM conv:selected-visits) and the accepted rows' modules listed in 3.
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/cv-lem-carriers-reviewer-input-statement.lean.txt
   (module CV/CarriersLemma.lean: module docstring with the notation map and the review note — verify, do not trust; the
   bundle `CV.CarriersData` (fields traversal_circle, count, noncrossing, nonadjacent_together, piece_carrier) and the
   theorem `CV.carriers`; auxiliary definitions pieceOwner etc. are library material; helper lemmas' proofs not under
   review). Do NOT open work/lean/CV/CarriersLemma.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/Carriers.lean (accepted-
   candidate rows def:smoothing / def:wind / def:pieces: Piece, pieceOf, pieceLabels, residualGraph), CV/Events.lean
   (Ind, N, U, geometric interlacement on CrossingGeometry), CV/Setup.lean (Diagrammatic), CV/CarrierBridges.lean,
   SM/FlatCarriersDefs.lean (GeoComponent, geoOwner, geoSmoothingSuccessor, geoComponentMarkList — the accepted
   def:flat-carriers geo layer), SM/GeoCarrierCrossings.lean (geoSupportNeighbors / geoSupportUnselected — definitions),
   SM/GeometricVisits.lean (geometricVisitPosition), SM/Traversal.lean (TraversalPoint, traversalEvaluation,
   traversalBetween), SM/Crossings.lean (Crossing, Visit, crossingPoint), SM/GeometricInterlacement.lean.

YOUR TASK: decide whether the bundle pins down exactly the printed lemma on its printed binder (hD : Diagrammatic P,
S ∈ Ind — d1:363-365 "genericity is not needed here"). Setup sentence ("the traversal circle Γ …, each double point has
exactly two preimages, so Γ carries 2m marked points"): field traversal_circle — is it exactly that sentence (the
fibre characterisation of crossing points, two visits per crossing, injectivity of visit positions, |visits| = 2|crossings|)
or does it add/omit? (i) "exactly |S| + 1 carriers" (count). (ii) noncrossing — ROUND 2: after round 1 found the clause narrowed to crossing visits, it is now stated over
all MARKED points of the traversal circle (Mark P = the original vertices and the crossing visits, the points the
accepted carriers of def:smoothing own), with 'preimage of an element of S' = a visit of a selected crossing, and
the two traversalBetween conditions for 'in this cyclic order' — is this exactly the printed clause on the accepted
finite model (unmarked interior points of edges have no owner in that model — judge whether that residual gap is
inherent and non-blocking)? (iii) the two visits of an undominated crossing (not in S, not
adjacent to S) lie on one carrier (nonadjacent_together — hypotheses as printed?). (iv) every residual piece H lies on
exactly one carrier (piece_carrier: ∃! carrier owning all visits of all crossings of H — is "exactly one" printed or is
"one" printed? existence versus uniqueness). Expand definitions to primitives; say where the Lean is STRONGER or WEAKER;
default to "not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
