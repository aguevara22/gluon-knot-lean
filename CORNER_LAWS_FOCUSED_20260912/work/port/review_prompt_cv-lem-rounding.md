You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row of the CV lane against ONE printed source statement of the paper "CV"
(reference/R/CV/, frozen): CV:lem:rounding (row 152), Lean declaration `CV.rounding : CV.CVRoundingData`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-lem-rounding-source-excerpt-lines-31-93.tex.txt (= reference/R/CV/d3_floor.tex 31-93:
   the lemma "rounding" of the CV paper with its hypotheses, the clearance sentence, the output sentence, clauses (a)-(e) and two
   commentary paragraphs). Context, ONLY to fix notation: d3_floor.tex 94-303 (its proof — skim for the objects), 304-330
   (CV:lem:curl, consumer), 736-800 (CV:thm:carrierfloor, clauses (A)-(C) — how the rounding is consumed; (C) states the no-triple
   provenance), reference/R/CV/d1_setup.tex 220-238 (def:generic), 316-320 (def:diagrammatic), 726-760 (def:rot: the computable
   rotation number of a regular polygon), 1-60 (def:polygon, def:regular if there), reference/SM/sm-3-statesum.tex 3644-3694 (the SM
   paper's cf:lem-rounding, accepted as SM.cf_lem_rounding — the Lean row under review is proved from it; the two printed lemmas are
   nearly word-identical: compare them yourself and note every difference).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/cv-lem-rounding-reviewer-input-statement.lean.txt (module
   CV/Rounding.lean: the bridge definitions polyComp, OverUnder (an over/under assignment on a labelled polygon), toPolygonDiagram /
   ofPolygonDiagram / ofDiagram, clearance, roundingAdmissible, roundingRecord, rotCurve, the bundle CVRoundingData with fields
   exists_clearance, smooth_regular_carried, a, b, c, d, e, and theorem CV.rounding are UNDER REVIEW; helper lemmas' proofs are not).
   Its module docstring maps the printed notation — verify, do not trust. Do NOT open work/lean/CV/Rounding.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/Rounding.lean ONLY its statement part
   (the same text as work/drafts/rounding/Rounding_statement_FINAL.lean, which you MAY read instead: PolygonDiagram, cornerDisc /
   subsegOut / subsegIn / polygonImage, SmoothRegularLoop, Carried, RoundingWitness, RoundingData — the accepted SM row's vocabulary; do
   not read the construction §7-§10), SM/FrontSmooth.lean (SmoothLoop), SM/TurnLift.lean, SM/RotationNumber.lean (ClosedC1Curve.rot,
   rotationNumber, principalTurn), CV/Setup.lean (LabelledTuple, IsPolygon, Regular / regular_iff_sm, Generic, Diagrammatic and its
   clauses, Diagrammatic.crossingGeometry), CV/Rotation.lean (CV.rot — the accepted CV:def:rot — and rot_eq_rotationNumber if present),
   CV/Events.lean (selfIntersections, crossingPoint lemmas), SM/LinkDiagram.lean (Shadow.single, Diagram, Generic, Crossing, Visit,
   crossingPoint, sign, writhe), SM/Polygon.lean (edge, edgeSegment, det, Plane), SM/EuclideanPlane.lean, SM/LinkMoves.lean (IsDisc).
   You MAY read work/AUTHOR_NOTES.md entries "Rounding lane (cf:lem-rounding, row 97)" and "cf:lem-rounding ACCEPTED" (2026-09-14) for
   the recorded SM readings FR-R1..FR-R7 and the pre-review notes R-a..R-h, and the CV-DOM decision entry ("CV-DOM decided", readings
   (i)-(iii), decision F2: no narrowing of CV rows).

DISCLOSED READINGS of the unit (judge each): FR-R1 the smooth diagram D_ε is the polygonal diagram D carried by the smooth curve
(Carried); FR-R2 the printed ∃-form; FR-R3 the witness exports more than printed; FR-R4 arclength/Λ parameter; FR-R5 the clause
fields are projections of the SM witness. CV-specific: FR-CV1 `OverUnder` is a new two-field structure for "an oriented diagram whose
underlying plane curve is L" on a labelled polygon (round trip with SM's PolygonDiagram is an identity); FR-CV2 the binder `[NeZero n]`
(CV's convention; n ≥ 3 is derived from Regular, no hn added); FR-CV3 the hypothesis `hreg : Regular L` is redundant given
Diagrammatic for n ≥ 3 but kept because it is printed; FR-CV4 no-triple is supplied by `Diagrammatic` (CV's own class; thm:carrierfloor
(C) says so), not silently added; FR-CV5 CV.rot needs Regular; (d) is stated as rotCurve = (CV.rot L hreg : ℝ) with CV's own def:rot and
proved via the accepted rot_eq_rotationNumber; FR-CV7 "same strands" in SM's occurrence vocabulary.

YOUR TASK: compare the printed CV lemma clause by clause with the bundle (expand every definition to primitives): the hypotheses
(labelled polygon L : LabelledTuple n with Diagrammatic L — is that exactly "finitely many double points, all transversal, none a
corner, no corner on a non-incident edge"? plus Regular and nonzero principal turns (CV's τ_i); an over/under assignment OverUnder);
the clearance sentence (ε₀(L) depends on L alone; quantifier order); the output sentence (C^∞ regular closed curve L_ε, the diagram
D_ε carried by it); (a)-(e) exactly as CV prints them (note CV's single def:rot for (d), and whether every CV sub-clause has a
field and every field a CV sub-clause or a disclosed extra); the two commentary paragraphs (are they clauses or commentary?). Say
where the Lean is STRONGER or WEAKER; any printed clause without a Lean counterpart or Lean clause without a printed counterpart
(beyond the disclosed extras) is a discrepancy (label non-blocking ones). Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
