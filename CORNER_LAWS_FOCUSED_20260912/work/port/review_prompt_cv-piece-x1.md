You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE row of the CV lane against ONE printed source statement of the paper "CV"
(reference/R/CV/, frozen). The row is named in your task.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: CV:def:piecediagram → work/reviews/cv-def-piecediagram-source-excerpt-lines-565-590.tex.txt
   (= reference/R/CV/d1_setup.tex 565-590); CV:lem:piececurve → work/reviews/cv-lem-piececurve-source-excerpt-lines-592-610.tex.txt
   (= d1_setup.tex 592-610, the statement; its printed proof 611-667 may be read ONLY to learn which objects the statement
   names — Steps 1-5, the support K_H, the carrier q_H, the closed plane curve, its double points and Gauss word);
   CV:def:X1 → work/reviews/cv-def-X1-source-excerpt-lines-908-930.tex.txt (= d1_setup.tex 908-930). Context, ONLY to fix
   notation: d1_setup.tex 355-361 (def:smoothing), 362-383 (lem:carriers, accepted as CV.carriers), 450-459 (lem:carrierword,
   CV.carrierword), 487-530 (def:wind, def:pieces: U(S), residual graph, pieces — accepted CV:def:pieces), 726-760
   (def:rot: the rotation number, computably — accepted as CV.rot_definition if present in CV/Rotation.lean), 220-238 (def:generic), 316-320 (def:diagrammatic),
   reference/R/CV/d10_axioms.tex (ax:homfly, accepted as CV.ax_homfly, only if a clause cites it), reference/SM/sm-1-polygons.tex
   240-268 (def:gauss). You MAY read the executor's CV-DOM decision in work/AUTHOR_NOTES.md (entry "CV-DOM decided: F2 mechanism
   = (C) on the accepted geo layer", 2026-09-14, readings (i)-(iii)) and the disclosed readings of this unit listed below.
2. The Lean statements with the row proofs replaced by `sorry`: rows 142 and 143 → work/reviews/cv-piece-reviewer-input-statement.lean.txt
   (module CV/PieceCurve.lean: bundles PieceDiagramData / PieceCurveData, theorems CV.piecediagram_definition / CV.piececurve;
   the definitions StepInvariant, exists_pieceSupport (statement), pieceSupport, pieceCarrier, pieceCurve, pieceShadow,
   pieceDiagram, pieceHomfly, pieceWrithe, carrierGaussList-based Gauss words are UNDER REVIEW as part of the statements;
   helper lemmas' proofs are not under review); row 146 → work/reviews/cv-X1-reviewer-input-statement.lean.txt (module
   CV/X1.lean: groupedPoly, groupedWrithe, carrierR, slot, Omega1, X1, bundle X1DefinitionData, theorem CV.X1_definition).
   Their module docstrings map the printed notation — verify, do not trust. Do NOT open work/lean/CV/PieceCurve.lean or
   work/lean/CV/X1.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/Carriers.lean (Piece, pieceLabels,
   piecesOn, pieceOwner, residualGraph, U, N, wind — accepted rows CV:def:smoothing / def:wind / def:pieces), CV/CarriersLemma.lean
   and CV/CarrierWord.lean (statements of CV.carriers, CV.carrierword; carrierGaussList), CV/Setup.lean (Diagrammatic, Generic,
   Generic.diagrammatic), CV/Events.lean (Ind, N, U), CV/Axioms.lean (AxHomflyData, CV.ax_homfly — accepted), CV/RecordHomfly.lean
   (accepted), CV/Rotation.lean (rot, rotAbs — CV:def:rot if accepted there), SM/FlatCarriersDefs.lean (GeoComponent, geoOwner,
   geoSmoothingSuccessor, TracedSuccessor, geoComponentMarkList), SM/GeoCarrierCrossings.lean (geoCarrierCrossings),
   SM/GeoCornerPolygon.lean (geoCornerPolygon — the carrier as a closed polygon), SM/GeoCarrierSelfIntersections.lean
   (GeoIsSelfIntersection), SM/GeoPositiveLift.lean (geoPositiveLift — the actual positive diagram of a carrier; and the accepted
   positiveLift it equals), SM/GeoCarrierCount.lean (GeoInheritsMarkOrder), SM/GeometricVisits.lean (geometricGaussList),
   SM/LinkDiagram.lean (Diagram, Shadow, Generic, IsPositive, sign, writhe, componentCount), SM/LinkDiagramRecord.lean
   (Diagram.record, SingleCircle if there), SM/LinkInterfaces.lean (homfly), SM/LinkLaurentRing.lean (R, coeffAt), SM/Polygon.lean,
   SM/RotationNumber.lean (rot of a regular polygon).

DISCLOSED READINGS of the unit that stated these rows (judge each; none is a scope change): (R-a) `hn : 3 ≤ n` is a parameter
of the bundles (CV fixes n ≥ 3 globally; `Diagrammatic` alone does not give n ≥ 3 as a lemma), not of pieceSupport /
pieceCarrier / pieceCurve; (R-b) the recursion of lem:piececurve (Steps 2-5: smooth one double point outside H at a time)
is rendered by `StepInvariant` (K ⊆ U(S), K ∩ H = ∅, S ∪ K independent) with the measure "number of unselected crossings",
and the terminal support K_H = `pieceSupport` is fixed by Classical.choose from the existential `exists_pieceSupport` (the
printed step's choice of the next double point d is equally free); (R-c) "the Gauss word of the piece curve" is the
double-point subword of the carrier's inherited word (`carrierGaussList` filtered to H) — equal to P's Gauss word restricted
to H; (R-d) X₁ sums over `(Ind hP).attach` as the accepted SM.cornerStateSum does; (R-e) the piece diagram is
`geoPositiveLift` of the piece carrier (the actual positive diagram, every crossing positive by the divide convention).

YOUR TASK: for YOUR row only, decide whether the definitions + bundle render exactly the printed statement.
 CV:def:piecediagram — "the parent curve P with every double point outside H erased — the two strands drawn as passing
 without interaction — and every double point of H resolved by the divide convention: the branch whose direction u_over
 satisfies … is over" (fields erased, divide_convention: is `pieceDiagram`'s shadow the piece curve with exactly H's double
 points, one component, and IsPositive at every crossing the printed divide convention?), "positive" (every sign +1), "its
 writhe equals |H|" (writhe), "P_H its HOMFLY polynomial in the normalization of ax:homfly" (piece_polynomial: is naming
 the two normalising identities of ax:homfly here faithful?), the printed datum sentence(s) and any sentence about the record
 or the single circle (datum, record_shadow) — read 565-590 sentence by sentence and match each field.
 CV:lem:piececurve — the printed statement 592-610 (a residual piece H of a diagrammatic P with support S: a closed plane
 curve whose double points are exactly H, obtained by further smoothings, with Gauss word = restriction, realizable …):
 fields carriers_of_S, initial_carrier, step, step_well_defined, terminal, closed_plane_curve, double_points, gauss_word,
 realizable — are the recursion fields (step, step_well_defined, terminal) printed clauses (the statement, or the proof's
 Steps 1-5 turned into fields?) — a field that renders only a proof sentence is a discrepancy to be labelled; is
 `SM.Regular (pieceCurve …) ∧ (pieceShadow …).Generic` the printed "closed plane curve … generic"?
 CV:def:X1 — "the slot 1 − w_{S,L} − R(L)", "the factor Ω₁ = [a^{slot} z^0] P_{S,L}", "X₁ = Σ_S wind(S) ∏_L Ω₁": the grouped
 polynomial P_{S,L} = ∏_{H on L} P_H and grouped writhe w_{S,L} = Σ |H| (empty conventions 1 and 0), pieces assigned to
 carriers by lem:carriers (iv) (assigned_by_carriers_iv), R(L) = |rot L| (carrierR via rotAbs of the corner polygon; the
 rotation of the carrier as a closed polygon — is that def:rot?), coeffAt slot 0 = the coefficient of a^{slot} z^0, the
 state sum, and the field homfly_exists : AxHomflyData ("that such a polynomial exists at all is Axiom ax:homfly" — is a
 field restating the accepted axiom's clauses inside this definition faithful, stronger, or a documentation item?).
Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; any printed clause without a Lean counterpart
or Lean clause without a printed counterpart is a discrepancy (label non-blocking ones "non-blocking"). Default to "not
faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).

ROUND 2 (CV:lem:piececurve only; rows 142 and 146 are not under review in this round — 146 is accepted, 142 was reviewed
faithful). Round 1 found the row NOT FAITHFUL (one reviewer, both refuters): the printed last conclusion "the datum of Definition
def:piecediagram is the datum of C_H" (d1:608-609) has a rotation-system half — the parent's per-crossing counter-clockwise half-edge
order restricted to the surviving half-edges (d1:577-585; proof d1:664-666 "that is the second half of the datum") — which had no
field. REPAIR (statement changed; everything else in the module byte-identical, see work/drafts/cvdom/U7c-fix/REPORT.md which you
MAY read): a new field `rotation_system` — for every c ∈ H and every crossing x of the piece shadow at crossingPoint c, the two
strands of x are in bijection with the two parent edges of c with positively proportional directions (`dir s = t • edge P i`, t > 0),
hence the same counter-clockwise half-edge order at c — and `realizable` strengthened to a crossing-point-preserving bijection
`∃ e : (pieceShadow …).Crossing ≃ {c // c ∈ H}, ∀ x, crossingPoint x = crossingPoint (e x).1`. Judge in particular whether the
direction form renders the printed rotation system (a reviewer may prefer the literal "sub-half-edge" containment reading — say
whether that is needed for fidelity or only a stronger form), and re-check every other field of PieceCurveData.
