You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
cf:lem-curl (row 98), Lean declaration `SM.cf_lem_curl : SM.CurlData`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cf-lem-curl-source-excerpt-lines-3870-3891.tex.txt (= reference/SM/sm-3-statesum.tex
   3870-3891, the lemma "exact negative-curl replacement" with its hypotheses and clauses (i)-(iv)). Context, ONLY to fix notation and
   to see which objects the statement names: sm-3:3892-4280 (its proof — skim: the rational model, the chart, the affine fit, the collar,
   the polygonal kink), 3644-3694 (cf:lem-rounding, accepted as SM.cf_lem_rounding — the vocabulary SmoothRegularLoop / Carried / the
   junction lifts), 4282-4330 (cf:thm-carrierfloor, the consumer: which shape of the curl lemma it uses, 4442-4445), 325-351
   (def:positive-lift: the polygonal class; RI moves), 1825-1841 (ng:front-domain) if needed.
2. The Lean statement: work/reviews/cf-lem-curl-reviewer-input-statement.lean.txt — the STATEMENT part of the module SM/Curl.lean (its
   sections 1-4 verbatim: RecordCarried, CurlSite, CurlWitness (one field per printed sub-clause), CurlData (fields exists_curl, disc,
   i, ii, iii, iv), and the row theorem `cf_lem_curl : CurlData` with its proof withheld). It compiles. Every one of these declarations
   occurs byte-identically in the proof module (verified by script) whose other ~8000 lines are the construction and are NOT under
   review. Do NOT open work/lean/SM/Curl.lean or anything under work/drafts/curl/ except the files named below.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/Rounding.lean ONLY its statement part
   (= work/drafts/rounding/Rounding_statement_FINAL.lean, which you may read instead: SmoothRegularLoop, Carried, RoundingWitness), SM/FrontSmooth.lean
   (SmoothLoop), SM/TurnLift.lean and SM/RotationNumber.lean (ClosedC1Curve.rot, IsLiftOn), SM/LinkDiagram.lean (Diagram, Crossing, Visit,
   twin, crossingPoint, sign, writhe), SM/LinkDiagramRecord.lean (visitCoord, cycBetween), SM/LinkMoves.lean (RI / RIData — the accepted
   polygonal Reidemeister-I move — IsDisc, Clean), SM/LocalPolynomial.lean (P), SM/PolynomialBlock.lean (P_reidemeister_I — statement),
   SM/EuclideanPlane.lean, SM/Polygon.lean.

DISCLOSED FIDELITY RISKS recorded by the executor BEFORE the row was stated (work/AUTHOR_NOTES.md entries "Curl lane (cf:lem-curl, row
98)" and the follow-ups of 2026-09-14 — you MAY read them; also work/drafts/curl/PLAN_FINAL.md §5 and PREREVIEW.md): FR-C1 (the one
class deviation) the input and output diagrams are RecordCarried F D = the accepted Carried minus the point-coincidence clause plus
twin_eval — a polygonal RI kink of D cannot sit at the smooth double point; coherent with the record-level SmoothFront.Marking and with
the printed proof's record-isomorphism step; P is well defined at record level; the pre-review's mitigation was ADOPTED: the witness
field old_crossingPoint states that every OLD crossing of the kinked diagram keeps its point; FR-C2 exists_curl strengthens the printed
∃Δ to "inside any preassigned neighbourhood Δ₀ of p" (the printed proof does this and the consumer needs it); the bare printed form is
exists_curl'; FR-C3 "modified inside Δ" = equality of the parametrised curves with velocity off the window (s₁,s₂) mod 1; FR-C4
P_{F'} = P_F via the polygonal RI (accepted P_reidemeister_I); FR-C5 "isolated" = uniqueness of the u-tangency on the arc, "turns
strictly positively" = StrictMonoOn of a lift, β − α < 1; FR-C6 exports beyond print (window, unchanged_deriv, crossing
correspondences, ri : RI D D', sign/writhe corollaries); FR-C9 the polygonal kink is inserted at a free interior edge point in the
cyclic gap of t₀ — the smooth double point and the polygonal kink point are unrelated; the RI disc of `ri` carries no relation to Δ.

YOUR TASK: compare the printed lemma clause by clause with CurlSite (the hypotheses: a C^∞ regular closed curve F with a carried
diagram D, a direction u, a point p = F(t₀) with tangent direction u, isolated, an embedded arc through p containing no double point,
on which the tangent turns strictly positively …), the existence sentence (∃ Δ, F', D' …), and clauses (i) F' = F outside Δ with the
same diagram data off Δ and P_{F'} = P_F, (ii) no tangent u in Δ and exactly one tangent −u, (iii) exactly one double point in Δ, the
kink, negative, (iv) rot F' = rot F − 1 and w(D') = w(D) − 1 — expanding every definition to primitives. Every printed clause must have a
field and every field a printed clause or a disclosed extra; the record-level class (FR-C1) must be judged explicitly: is it a
faithful rendering of "a diagram carried by the curve" for THIS lemma, given the mitigation field, or a blocking class change? Say where
the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
