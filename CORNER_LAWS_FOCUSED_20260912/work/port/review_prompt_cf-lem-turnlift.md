You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cf-lem-turnlift-source-excerpt-lines-3542-3578.tex.txt (=
   reference/SM/sm-3-statesum.tex 3542-3578, cf:lem-turnlift: clauses (i), (ii), (iii)). Context, ONLY to fix
   notation: reference/SM/sm-3-statesum.tex 3579-3643 (its printed proof — to understand the intended models
   of "orientation-preserving reparametrisation", "continuous homotopy through direction loops", "regular
   homotopy", "regular arc", "compatible tangent-angle lift", "replacing b by c", "GL⁺(2) path"), 3514-3541
   (cf:def-turning, the ACCEPTED definitions this row uses), reference/SM/sm-1-polygons.tex lem:rot and
   def:regular (grep `label{lem:rot}`, `label{def:regular}`: the regular locus 𝓡_c, principal turns, positive
   flat subdivision, reversal, three-corner polygons).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/cf-lem-turnlift-reviewer-input-
   statement.lean.txt (module SM/TurnLift.lean: the MODELS `IsLiftOn`, `Reparam` (φ continuous, StrictMono,
   φ(s+1) = φ(s)+1), `DirectionLoop.reparam`, `DirectionHomotopy` (H : ℝ×ℝ → Plane, each H(t,·) a direction
   loop), `RegularHomotopy` (Γ, Γ′ jointly continuous, HasDerivAt in s, Γ′ ≠ 0, periodic; `curve t`,
   `tangentHomotopy`), `ClosedC1Curve.reverse`, `GLPlusPath`, the bundle `TurnLiftData` (17 fields) and the main
   declaration `SM.turnlift`); helper lemma proofs are not under review. Its module docstring and the plan
   work/drafts/TurnLift_PLAN.md (which you MAY read: clause → field → model → API) map notation — verify, do not
   trust. Do NOT open work/lean/SM/TurnLift.lean.
3. Lean definition modules (definitions and docstrings): work/lean/SM/TurningNumber.lean (accepted row
   cf:def-turning: DirectionLoop, IsSeamLift, lift, tw, shift, ClosedC1Curve, tangentLoop, rot, R),
   work/lean/SM/RotationNumber.lean and RotationTheorem.lean (rotationNumber, principalTurn; the accepted lem:rot
   bundle `SM.rotation_number` — statement only), RegularLocus.lean (Regular, insertVertex?, reversal — grep),
   EuclideanPlane.lean (Plane, det, euclideanLength, normalize).

YOUR TASK: decide whether the bundle pins down exactly the printed lemma, clause by clause. (i) "Every
continuous direction loop has a tangent-angle lift" (exists_tangent_angle_lift); "the integer tw(T)"
(tw_integer); "independent of the lift and seam" (tw_lift_independent, tw_seam_independent); "unchanged by an
orientation-preserving reparametrisation" (tw_reparam — is `Reparam` (continuous strictly increasing φ with
φ(s+1) = φ(s)+1) exactly an orientation-preserving reparametrisation of the circle ℝ/ℤ? does it cover all of
them, e.g. those not fixing 0? together with seam independence?); "constant under a continuous homotopy through
direction loops" (tw_homotopy — is `DirectionHomotopy` with t ∈ ℝ the printed [0,1]-homotopy (the plan says
the [0,1] case is the projIcc instance — is that a faithful covering of the printed clause?); "Consequently
the rotation of a closed C¹ regular curve is invariant under regular homotopy" (rot_regular_homotopy — is
`RegularHomotopy` the standard notion: a homotopy through C¹ regular curves with continuously varying
derivative?) "and reversing its orientation negates it" (rot_reverse). (ii) "2π rot(L) = Σ ϑ_i" and the
consequences (polygon_two_pi_rot, polygon_path_constant, polygon_subdivision, polygon_reversal,
polygon_triangle) — restated from the accepted lem:rot: check the exact printed wording (paths in 𝓡_c; positive
flat subdivision; orientation reversal; three-corner polygons ±1 by the common sign) and whether the fields
carry hypotheses the printed text does not (3 ≤ n? Regular?). (iii) "a closed C¹ regular curve obtained from L
by replacing every corner by a regular arc whose compatible tangent-angle lift has increment ϑ_i has rotation
rot(L)" (rounding — the subdivision model a k ≤ b k ≤ a (k+1), corner arcs with lift increment principalTurn L k,
straight pieces along edge k: is this exactly the printed "obtained from L"?); the arc replacement identity
rot(F_c) − rot(F_b) = (Δ_c − Δ_b)/2π (replacement — the model: arcs on [0,λ] of F_b and [0,μ] of F_c,
complementary arc shared up to a monotone ψ with ψ λ = μ, ψ 1 = 1, equal tangents T_Fb s = T_Fc (ψ s): does it
capture "regular oriented arcs having the same endpoints and the same oriented tangent rays at both endpoints,
replacing b by c in a closed curve gives closed C¹ regular curves F_b, F_c; compatible tangent lifts with equal
initial values"?); "applying A ∈ GL⁺(2) via a supplied path A_t with A_0 = I, A_1 = A to both arcs leaves
Δ_c − Δ_b unchanged" (glplus_invariance — arcs as nonvanishing tangent paths with common oriented end rays; is
the printed statement about the arcs' tangent data captured?). Every model is a READING of informal printed
notions: judge each for faithfulness (neither narrower nor wider than the printed notion in a way that changes
content), and say explicitly which readings you accept. Expand definitions to primitives; say where the Lean is
STRONGER or WEAKER; default to "not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
