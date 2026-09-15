You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE definition row against ONE printed source definition (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cf-def-turning-source-excerpt-lines-3514-3541.tex.txt (=
   reference/SM/sm-3-statesum.tex 3514-3541, cf:def-turning). Context, read ONLY to fix notation:
   reference/SM/sm-3-statesum.tex 3542-3643 (cf:lem-turnlift, the consumer: its clause (i) proves the lift
   existence and the independence claims; not under review), reference/SM/sm-1-polygons.tex (lem:rot: grep
   `label{lem:rot}` — the polygon rotation number rot(L) = Σ principal turns / 2π and the regular locus 𝓡),
   and reference/R/CV/d1_setup.tex 767-787 (CV def:rot's paragraph "Direction loops and smooth curves", the
   same definitions; the executor's decision F6 says they are defined once, here).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/cf-def-turning-reviewer-input-
   statement.lean.txt (module SM/TurningNumber.lean: definitions DirectionLoop, IsSeamLift, IsLift, lift, tw,
   ClosedC1Curve, tangentLoop, rot, R, polygonR, with supporting lemmas (proofs not under review), the bundle
   `TurningDefinitionData` and the main declaration `SM.turning_definition`). Its module docstring and the plan
   it cites map notation — verify, do not trust. Do NOT open work/lean/SM/TurningNumber.lean.
3. Lean definition modules (definitions and docstrings): work/lean/SM/EuclideanPlane.lean (Plane, euclideanLength,
   planeComplex), work/lean/SM/RotationNumber.lean (rotationNumber, principalTurn; the accepted lem:rot bundle
   `SM.rotation_number` — statement only), work/lean/SM/RegularLocus.lean (Regular), and Mathlib's
   Circle / IsCoveringMap definitions if needed (work/lean/.lake/packages/mathlib/Mathlib/...).

YOUR TASK: decide whether the definitions + bundle pin down exactly the printed cf:def-turning, sentence by
sentence: a direction loop (continuous map of the circle ℝ/ℤ to the unit circle S¹ — rendered as a 1-periodic
continuous T : ℝ → Plane of unit length: exact?); a tangent-angle lift θ (continuous on [0,1] with T = (cos θ,
sin θ) — `IsSeamLift`; the Lean also has a global-lift device `IsLift` and `lift := Classical.choose` of a
global lift: is `tw := (lift 1 − lift 0)/2π` the printed tw(T) = (θ(1) − θ(0))/2π for ANY printed lift θ? the
bundle claims so — check the field); tw is an integer; a closed C¹ regular curve γ (1-periodic, differentiable,
nonvanishing derivative — is C¹ (continuous derivative) required and rendered?); rot(γ) := tw(γ'/|γ'|) via
`tangentLoop`; "for a polygon in the regular locus, rot remains that of lem:rot" (rendered as: the polygon
rotation is the accepted rotationNumber — is that the printed sentence's content, or does the sentence require
a polygon-to-direction-loop comparison?); R := |rot| for either. Is anything printed missing (e.g. the seam
independence, the reparametrisation invariance — which belong to cf:lem-turnlift (i), not to the definition)?
Is anything in the bundle unprinted? Expand definitions to primitives; say where the Lean is STRONGER or
WEAKER; default to "not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
