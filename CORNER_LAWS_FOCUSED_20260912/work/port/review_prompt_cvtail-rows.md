You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statements
you are reviewing and you must not read their proofs. Your job is a statement-fidelity review of ONE row against its
printed source; the row is named in your task: CV:thm:carrierfloor (row 155, `CV.carrierfloor : CV.CarrierFloorData`,
module CV/CarrierFloor.lean), CV:singleton_D_i (row 165, `CV.singleton_D_i : CV.SingletonDiData`, module CV/SingletonDi.lean),
or R:extreme_pair_zero (row 175, `RProof.extreme_pair_zero`, module RProof/ExtremePairZero.lean; a package obligation with a
FIXED name and a FIXED bundle statement `ExtremePairZeroData` accepted earlier in the R lane).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. Printed sources, verbatim: row 155 — work/reviews/cv-thm-carrierfloor-source-excerpt-lines-736-807.tex.txt (= reference/R/CV/
   d3_floor.tex 736-807, Theorem thm:carrierfloor, clauses (R)(A)(B)(C)(D)); row 165 — work/reviews/cv-singleton-d-i-source-excerpt-
   lines-2660-2700.tex.txt (= reference/R/CV/d6_vertexedge.tex 2660-2700; the row is the CLAUSE (D)(i) of thm:s7universal at line
   2682: "Let S ∈ Ind(G_P), let A be a uniform carrier of S, and let {c} be a singleton residual piece of S carried by A. Then
   min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2, so the factor Ω₁(S,A) of Definition def:X1 is zero"); row 175 — work/reviews/
   r-extreme-pair-zero-source-excerpt-R_EXTREME_PAIR_ZERO_PROOF.md.txt (= reference/R/RA/R_EXTREME_PAIR_ZERO_PROOF.md, whole file)
   read with R_ASSEMBLY_SPEC.md and EXECUTION.json (the obligation's place in the R assembly). Context ONLY to fix notation: the SM
   theorem cf:thm-carrierfloor (reference/SM/sm-3-statesum.tex 4282-4339) and its accepted Lean statement (work/reviews/
   carrier-floor-statements-reviewer-input.lean.txt §2-§6) — row 155's (R)(A)(B)(C) are SM's clauses read through the CV polygon
   bridge (the plan's rule F6, as the accepted CV:lem:rounding / CV:lem:uniformrot / CV:lem:curl were); reference/R/CV/d3_floor.tex
   304-330 (CV:lem:curl) and the CV definitions def:rot, def:diagrammatic, def:X1, def:eligible, def:wind (grep in reference/R/CV/).
2. The Lean statements: work/reviews/cv-thm-carrierfloor-reviewer-input-statement.lean.txt (CV/CarrierFloor.lean with proofs replaced
   by sorry: CV.CarrierFloorRData/AData/BData/CHyp/CData/DData, CV.CarrierFloorData, the bridges carrierfloor_*_of_sm — statements
   only —, CarrierSlotFloor, the row theorem), work/reviews/cv-singleton-d-i-reviewer-input-statement.lean.txt (CV/SingletonDi.lean
   stripped: SingletonPieceOn, SingletonDiData, SingletonSplitData, the row theorem; the cvt165s_ helpers are proof route, not under
   review), work/reviews/r-extreme-pair-zero-reviewer-input-statement.lean.txt (RProof/ExtremePairZero.lean stripped: the row theorem
   with the FIXED statement) and, for the fixed bundle `ExtremePairZeroData` and `RowShape`, work/reviews/r-ledgers-reviewer-input.lean.txt
   (RProof/RALedgers.lean stripped) plus the accepted RProof/X1Rows*.lean modules where ExtremePairZeroData is defined (grep).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/ (Setup, Rounding, Curl, UniformRot,
   GroupedKnot, X1, GeoCornerPolygon*, GeoPositiveLift*, PieceHomflyTransport, Axioms — grep for the names you meet), work/lean/SM/
   (CarrierFloor.lean statements, CornerStateSum, LinkLaurentRing (degAZ, mindegAZ, coeffAt), LinkInterfaces (homfly), LocalPolynomial (P),
   PolynomialBlock (P_eq_homfly)), work/lean/RProof/X1Rows*.lean (the accepted R rows 168/170/172/173 and their bundles, PRE_175_*),
   and Mathlib.
4. Disclosed readings: work/AUTHOR_NOTES.md entry "CV/R tail (rows 155, 165, 174-178, 183 Bridge:theorem, 184 …): design panel judged …"
   of 2026-09-15 (decisions D-CVT-1..6 and the fidelity risks FR-CV-155-1..9, FR-CV-165-1..4, FR-R-174..177, FR-R-178-1/2) and the
   entries "CV/R tail wave 1 assembled …" and the port entry; for row 175 also work/drafts/rlane2/NOTES_FINAL.md §7 (the accepted
   statement panel's clause map of ExtremePairZeroData — you MAY read this one draft file).

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing
RProof.ExtremePairZero if you wish): all three row theorems have no hypothesis beyond their printed binders; axioms exactly [propext,
Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]
(inherited from SM.cf_thm_carrierfloor, row 99) — all registered.

YOUR TASK. Row 155: compare (R)(A)(B)(C)(D) with the CV bundles: (R) on knots K (homfly X.reverse = homfly X for a one-component X, the
LinkEquiv reading, signs/writhe/rotation reversal with CV.rot / rotCurve), (A) the record Rnd = SM.Round through the polygon bridge with
its determinacy fields, (B) the tangency count on CV's printed binders (LabelledTuple L, Diagrammatic, Regular, OverUnder) for the
normalised orientation (FR-CV-155-5; the reversal branch on SM objects), (C) the hypotheses one per printed clause on CV's vocabulary and
the conclusion 1 − w − rotAbs ≤ mindegAZ (homfly X) with the f_D sentence, (D) on def:X1 objects: "L a carrier of S carrying no residual
piece, so that P_{S,L} = 1 and w_{S,L} = 0 by def:X1's empty conventions … all its principal turns are nonzero and … either every turn is
positive or exactly one is negative. Then R(L) ≥ 1 and min deg_a P_{S,L} = 0 ≥ 1 − w_{S,L} − R(L)" ↔ CarrierFloorDData; is the polygon
bridge faithful (the CV text's own scoping sentences "Here rot is as in def:rot"); is anything STRONGER or WEAKER. Row 165: compare the
clause with SingletonDiData (degree_gap in support form "∀ d, coeffAt d 0 (groupedPoly) ≠ 0 → slot + 2 ≤ d" — is this exactly
"min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2" with f_A = [z⁰]P_{S,A} (def:markeddata) and the slot 1 − w − R (def:X1)?; is the vacuous case
f_A = 0 handled as printed?; Omega1 = 0 as the second field; SingletonPieceOn = "a singleton residual piece of S carried by A" in def:X1's
sense (lem:carriers (iv)); "uniform carrier" = CV:def:wind's CarrierUniform). Row 175: the row theorem's statement must be the FIXED
accepted bundle form (`∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ` under the event hypotheses) — verify it is
byte-identical to the accepted X1Rows shape and compare ExtremePairZeroData's fields with R_EXTREME_PAIR_ZERO_PROOF.md's statement
("Its complete X1 term on the latter generic polygon is zero, for arbitrary outside support and exterior geometry" ↔ pair_row_zero, plus
the presupposition fields); is the instantiation from row 165 the printed route? Say where the Lean is STRONGER or WEAKER; label
non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite source and
statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of strings),
"supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
