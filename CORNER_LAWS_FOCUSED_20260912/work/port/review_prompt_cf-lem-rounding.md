You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
cf:lem-rounding (row 97), Lean declaration `SM.cf_lem_rounding : SM.RoundingData`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cf-lem-rounding-source-excerpt-lines-3644-3694.tex.txt (= reference/SM/sm-3-statesum.tex
   3644-3694, the lemma "rounding" with clauses (a)-(e)). Context, ONLY to fix notation and to see which objects the statement
   names: 3695-3869 (its printed proof: the profile φ, the junction arcs, the clearance ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X}, the
   discs; skim), 3870-3900 (cf:lem-curl, the first consumer), 4282-4310 (cf:thm-carrierfloor (A), "one curve and one diagram
   Round(L, D, ε)"), 325-351 (def:positive-lift: the polygonal class of oriented diagrams; generic = regular ∧ tail_off ∧
   transverse ∧ no_triple), 1825-1841 (ng:front-domain, for the smooth-curve vocabulary), reference/SM/sm-1-polygons.tex
   (def:polygon, def:regular, rotation number / principal turns if cited).
2. The Lean statement: work/reviews/cf-lem-rounding-reviewer-input-statement.lean.txt — the FIXED statement file (module
   header with the notation map; PolygonDiagram, cornerDisc / subsegOut / subsegIn / polygonImage, SmoothRegularLoop and its
   toClosedC1Curve, doublePoints, the record `Carried γ X` (a polygonal diagram carried by a smooth regular loop),
   `RoundingWitness C D ε` (one field per printed sub-clause of (a)-(e)), the bundle `RoundingData` (fields exists_clearance,
   smooth_regular_carried, a, b, c, d, e) and `theorem cf_lem_rounding : RoundingData := by sorry`). Every one of these
   declarations occurs byte-identically in the proof module SM/Rounding.lean (verified by script); the proof module's other
   ~4000 lines are the construction and are NOT under review. Do NOT open work/lean/SM/Rounding.lean or anything under
   work/drafts/rounding/.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/FrontSmooth.lean (SmoothLoop:
   C^∞ 1-periodic plane curves; Plane), SM/TurnLift.lean and SM/RotationNumber.lean (ClosedC1Curve, rot, tangentLoop,
   IsLiftOn, rotationNumber of a polygon, principalTurn), SM/LinkDiagram.lean (Shadow, Shadow.single, PolyComp, Diagram,
   Generic, Crossing, Visit, twin, crossingPoint, sign, writhe, dir), SM/LinkDiagramRecord.lean (visitCoord, cycBetween,
   VisitBetween), SM/LinkMoves.lean (IsDisc), SM/Polygon.lean (LabelledTuple, edge, edgeSegment, edgePoint, Regular),
   SM/EuclideanPlane.lean (det, euclideanLength, normalize), SM/CS3.lean only for `regular_adjacent_meet` if cited.

DISCLOSED FIDELITY RISKS recorded by the executor BEFORE the row was stated (work/AUTHOR_NOTES.md entry "Rounding lane
(cf:lem-rounding, row 97): design panel decided", 2026-09-14 — you MAY read it): FR-R1 D_ε is the polygonal diagram D
carried by the smooth curve (`Carried`: occurrence parameters, twin pairing, transversality, cyclic order via
cycBetween/visitCoord, over/under = D's with sign consistency) — the FR-1 reading of "a diagram carried by it"; FR-R2 the
bundle is the printed ∃-form (∃ ε₀ > 0 ∀ ε ∈ (0, ε₀) ∃ witness), the named construction lives in the proof module; FR-R3
`no_triple` enters through PolygonDiagram.generic (the accepted class of oriented diagrams), and the witness exports more
than printed (constant speed, the parametric straight form, occurrences on the OPEN straight parameter interval, curve
flatness of order ≥ 2 at the junction ends, "junction = all of the curve in the disc", embeddedness of each junction);
FR-R4 arclength/Λ parameter (period 1) instead of arclength σ ∈ [0, ℓ]; "angular derivative nonzero" as deriv θ ≠ 0 on the
open arc; FR-R5 fields a-e of RoundingData are projections of RoundingWitness, the theorem content is exists_clearance;
FR-R6/R7 chain and Mathlib notes (not statement matters). A statement pre-review (work/drafts/rounding/PREREVIEW.md, which you MAY read) found the structures jointly satisfiable and raised: R-a the lifts θ j are C^∞ on all of ℝ and constant on both half-lines (a witness device beyond the printed junction-only lift); R-b the subdivision a, b and the junction endpoints are proof objects promoted into the witness (a fixed parametrisation); R-c same_strand_dir renders the proof's 'with their orientations'; R-e the printed (e) is existential in the discs while the Lean fixes the radius-ε Euclidean discs (stronger); R-f the clearance must depend on L alone — the field exists_clearance was therefore restated BEFORE this review as ∀ C, turns ≠ 0 → generic shadow → ∃ ε₀ > 0, ∀ D ε, … (judge whether that is the printed ε₀(L)); R-h the seam convention (parameter 0 at the start of junction 0).

YOUR TASK: compare the printed lemma clause by clause with RoundingWitness and RoundingData, expanding every definition to
primitives. In particular: the input ("L a closed polygon with nonzero principal turns … D an oriented diagram whose
underlying plane curve is L" — PolygonDiagram C with (∀ i, principalTurn C.P i ≠ 0) and the accepted Generic: is any
hypothesis added or missing?); the clearance sentence; the output ("a C^∞ regular closed plane curve L_ε and a diagram D_ε
carried by it" — SmoothRegularLoop and Carried Lε D.toDiagram: is reading D_ε = D faithful, i.e. does the printed lemma
allow/require D_ε to be a different diagram?); (a) agreement outside the discs and the straight parts; (b) the junction
arcs: the lift θ, its monotonicity, the swept angle, each direction attained once, angular derivative nonzero, the flat ends
(iteratedDeriv = 0 at both ends for m ≥ 1) — is every printed sub-clause a field and every field a printed sub-clause or one
of the disclosed extras (FR-R3), and are the extras harmless strengthenings of the witness?; (c) same double points, same
strands and directions, same signs, same writhe; (d) rot(L_ε) = rot(L); (e) the discs: closed Euclidean ε-discs about the
corners, disjoint, off the non-incident edges, no double point inside, meeting the incident edges exactly in the
ε-sub-segments, containing the modification, the modification being the whole curve inside the disc, embedded. Say where
the Lean is STRONGER or WEAKER; any printed clause without a Lean counterpart or Lean clause without a printed counterpart
(beyond the disclosed extras) is a discrepancy (label non-blocking ones "non-blocking"). Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
