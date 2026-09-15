You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
CV:lem:curl (row 154), Lean declaration `CV.curl : CV.CVCurlData` (module CV/Curl.lean).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-lem-curl-source-excerpt-lines-304-323.tex.txt (= reference/R/CV/d3_floor.tex
   304-323, Lemma lem:curl "exact negative-curl replacement": the scoping sentence 305, hypotheses 306-311, existence sentence
   311-313, clauses (i)-(iv) 315-321). Context, ONLY to fix notation and to see which objects the statement names: d3_floor.tex
   324-701 (its proof — skim), 703-733 (the authorship remark rem:curlauthor — commentary), 885-912 (the consumer, CV:thm:carrierfloor
   (C): which shape of the curl lemma it uses), 31-93 (CV:lem:rounding, accepted as CV.rounding — the input class "a diagram D_ε
   carried by" the rounded curve); reference/R/CV/d1_setup.tex 726-786 (def:rot: one definition for polygons and for closed C¹
   regular curves), 522-531 (CV:def:record); reference/SM/sm-3-statesum.tex 3870-3891 (the SM twin lemma cf:lem-curl, accepted as
   SM.cf_lem_curl; its \status line 3890 says it is transcribed from CV lem:curl) if you want to compare the two printed texts.
2. The Lean statement: work/reviews/cv-lem-curl-reviewer-input-statement.lean.txt — the module CV/Curl.lean with EVERY theorem proof
   replaced by `sorry` (the row theorem `curl : CVCurlData`, the helper theorems and the corollaries `curl_of_carried`,
   `curl_homfly_eq`, `rotCurve_eq_sub_one` are all withheld); definitions (CurlSite, p, T, toSM, ofSM, ofCarried, CurlSite.next)
   are shown in full and ARE under review. It compiles. Its module docstring maps notation and tex lines — verify it, do not trust
   it. Do NOT open work/lean/CV/Curl.lean or anything under work/drafts/cvdom/.
3. Lean definition modules (definitions and docstrings; proofs not under review): the SM twin's STATEMENT part
   work/reviews/cf-lem-curl-reviewer-input-statement.lean.txt (SM.RecordCarried, SM.CurlSite, SM.CurlWitness — one field per printed
   sub-clause — SM.CurlData; CV's clauses are read on `SM.CurlWitness S.toSM Δ`, so you need these definitions; do NOT open
   work/lean/SM/Curl.lean itself), work/lean/CV/Rounding.lean (row 152: CV.rounding, its statement part; CV.RoundingWitness if named),
   work/lean/CV/RotationSmooth.lean (CV.rotCurve — decision F6: an `abbrev` of ClosedC1Curve.rot), work/lean/CV/Homfly*.lean or
   wherever `CV.homfly` / `P_eq_homfly` are defined (grep `def homfly` under work/lean/CV/), work/lean/SM/Rounding.lean ONLY its
   statement part (or work/drafts/rounding/Rounding_statement_FINAL.lean: SmoothRegularLoop, Carried, RoundingWitness),
   SM/FrontSmooth.lean (SmoothLoop), SM/TurnLift.lean and SM/RotationNumber.lean (ClosedC1Curve.rot, IsLiftOn), SM/LinkDiagram.lean
   (Diagram, Crossing, Visit, twin, crossingPoint, sign, writhe), SM/LinkDiagramRecord.lean, SM/LinkMoves.lean (RI / RIData, IsDisc,
   Clean), SM/LocalPolynomial.lean (P), SM/PolynomialBlock.lean (P_reidemeister_I — statement), SM/EuclideanPlane.lean, SM/Polygon.lean.

DISCLOSED FIDELITY RISKS (you MAY read work/AUTHOR_NOTES.md entries "Curl lane (cf:lem-curl, row 98)" of 2026-09-14 and the entry
"CV:lem:curl (row 154) ported"): inherited from the accepted SM twin — FR-C1 (the one class deviation: the input and output diagrams
are RecordCarried F D = the accepted Carried minus the point-coincidence clause plus twin_eval, because a polygonal RI kink of D
cannot sit at the smooth double point; the mitigation field old_crossingPoint says every OLD crossing of the kinked diagram keeps its
point; here argued CV-native since CV:def:record d1:522-531 is itself record-level and the consumer's R-fold iteration through
CurlSite.next needs input class = output class), FR-C2 (exists_curl strengthens the printed ∃Δ to "inside any preassigned
neighbourhood Δ₀ of p" — the printed proof does this and the consumer (C) needs it; the bare printed form is exists_curl'), FR-C3
("modified inside Δ" = equality of the parametrised curves with velocity off the window mod 1), FR-C4 (P_{F'} = P_F via the
polygonal RI and P_reidemeister_I), FR-C5 ("isolated" = uniqueness of the u-tangency on the arc; "turns strictly positively" =
StrictMonoOn of a lift with β − α < 1), FR-C6 (exports beyond print), FR-C9 (the polygonal kink is inserted at a free interior edge
point in the cyclic gap of t₀; the smooth double point and the polygonal kink point are unrelated). CV-specific — FR-CV-C1: CV.CurlSite
duplicates SM.CurlSite field for field (the printed hypotheses are word for word the same in both papers) so that CV's binder carries
CV's tex lines; toSM/ofSM are rfl round trips; the witness is NOT duplicated (CV's clauses are read on SM.CurlWitness S.toSM Δ, as row
152 read its clauses on SM.RoundingWitness); FR-CV-C2: the scoping sentence 305 "rot as in def:rot" — in this lemma every rot is a
curve rot (F, F' are C^∞ immersed circles; no polygon is named) and CV.rotCurve is definitionally ClosedC1Curve.rot (F6), so (iv) needs
no identification theorem; FR-CV-C3: the bundle states P_{F'} = P_F with the accepted P (axioms of CV.curl = the twin's: SM.lp_lm);
the polynomial in CV:def:homfly's letter `homfly` is the corollary curl_homfly_eq (adds SM.lit_homfly, SM.lp_lm_uniqueness through
P_eq_homfly) — judge whether "P_{F'}(a,z) = P_F(a,z)" printed in CV denotes CV's homfly or the accepted P, and whether keeping the
homfly form outside the bundle is faithful; FR-CV-C4: the consumer's entry (the Carried record of the all-switched rounded diagram)
is the consumer's obligation, not this row's; FR-CV-C5: same binder and quantifiers as printed, one field per printed sentence/clause.

YOUR TASK: compare the printed lemma clause by clause with CV.CurlSite (the hypotheses: a connected C^∞ immersed circle F with an
oriented diagram D carried by it, finitely many transverse double points, no triple points, a direction u, a point p = F(t₀) with
tangent u, isolated among such points, in an embedded arc containing no double point along which the tangent turns strictly
positively), the existence sentence (∃ Δ, F', D' — "modified inside a disc Δ meeting the rest of the diagram only in that arc"), and
clauses (i) F' again such an oriented diagram, P_{F'} = P_F, same double points outside Δ with the same signs, (ii) no tangent u in Δ
and exactly one tangent −u, (iii) exactly one double point inside Δ, negative, (iv) rot F' = rot F − 1 and w(F') = w(F) − 1 — expanding
every definition to primitives (through toSM into the SM witness fields). Every printed clause must have a field and every field a
printed clause or a disclosed extra; the record-level class (FR-C1) must be judged explicitly for THIS lemma in CV's own framework
(CV:def:record; the consumer's iteration). Say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not
faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
