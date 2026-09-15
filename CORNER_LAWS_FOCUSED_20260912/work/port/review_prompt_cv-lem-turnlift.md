You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma row of the CV lane, CV:lem:turnlift (row 145), against its printed
source (reference/R/CV/d1_setup.tex, frozen).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-lem-turnlift-source-excerpt-lines-789-822.tex.txt (= d1_setup.tex
   789-822, lem:turnlift: preamble "Here rot is as in Definition def:rot", clauses (i), (ii), (iii)). Context, ONLY
   to fix notation: d1_setup.tex 823-905 (its printed proof: the models of reparametrisation, homotopy, regular
   homotopy, rounding, arc replacement, GL⁺(2) paths), 726-787 (def:rot, accepted row 144), 8-40 (def:polygon,
   def:regular: 𝓡_c, principal turns τ_i, positive flat subdivision, reversal), reference/SM/sm-3-statesum.tex
   3542-3578 (SM cf:lem-turnlift, the same lemma in SM's wording, under separate review; decision F6: the
   direction-loop clauses are proved once, in SM/TurnLift.lean, and re-exported to CV).
2. The Lean statement with the row proofs replaced by `sorry`: work/reviews/cv-lem-turnlift-reviewer-input-
   statement.lean.txt (module CV/TurnLift.lean: bundle `TurnLiftFullData` (18 fields), `turnlift_full`, and the
   bridge theorems `rotCurve_eq_rot_of_rounding`, `turnlift_full_rot_eq_SM`). Do NOT open work/lean/CV/TurnLift.lean.
3. Lean definition/statement modules (definitions, docstrings and STATEMENTS only): work/lean/SM/TurnLift.lean
   (the SM models Reparam, DirectionHomotopy, RegularHomotopy, ClosedC1Curve.reverse, GLPlusPath and the bundle
   TurnLiftData whose fields the CV fields cite — read the statements, not the proofs), work/lean/SM/TurningNumber.lean
   (accepted cf:def-turning: DirectionLoop, IsSeamLift, tw, ClosedC1Curve, tangentLoop, rot, R), work/lean/CV/
   Rotation.lean and CV/RotationSmooth.lean (accepted row 144: epsRot, Admissible, rotRay, rot, rotAbs, turnlift_ii,
   TurnliftIIData, CV.tw / rotCurve / Rcurve aliases — statements only), work/lean/CV/Setup.lean (CV.Regular,
   CV.principalTurn, CV.regularLocus), work/lean/SM/RotationNumber.lean (rotationNumber, principalTurn).

YOUR TASK: decide whether the bundle pins down exactly the printed CV lemma, clause by clause, in CV's notation:
(i) the direction-loop clauses on CV.tw (existence of a lift; the integer tw independent of lift and seam;
unchanged by orientation-preserving reparametrisation; constant under homotopy through direction loops), the
regular-homotopy invariance and reversal negation of rot(γ) on CV.rotCurve — the models (Reparam: continuous
strictly increasing φ with φ(s+1) = φ(s)+1; DirectionHomotopy with t ∈ ℝ; RegularHomotopy; reverse) are the SM
models: judge them against CV's printed wording; (ii) "If L ∈ 𝓡_c has principal turns τ_i then 2π rot(L) = Σ τ_i"
on CV's ray-formula rot (polygon_two_pi_rot / polygon_two_pi_rotRay), the ray independence, and the consequences
(paths in 𝓡_c, positive flat subdivision, reversal, three-corner polygons ±1) — check hypotheses (Regular; any
c ≥ 3?) and the exact CV wording; (iii) rounding (rot of a C¹ curve obtained from L by replacing corners with
regular arcs of lift increment τ_i equals rot(L) — on CV's rot), the arc-replacement identity and the GL⁺(2)
invariance — the SM models restated: are they exactly CV's sentences? Note where CV's text differs from SM's
(the header claims only the preamble differs). Is anything printed missing, anything unprinted added (e.g.
polygon_ray_independent is printed in def:rot, not in the lemma — acceptable?). Expand definitions to primitives;
say where the Lean is STRONGER or WEAKER; default to "not faithful" if in doubt; label non-blocking discrepancies
"non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
