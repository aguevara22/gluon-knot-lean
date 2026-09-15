You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912
GENERAL RULES: read only the files listed; expand every local Lean definition to accepted
primitives; compare hypotheses, quantifiers, conclusions and definitions clause by clause; say
where the Lean is STRONGER or WEAKER than the source; any printed sub-clause without a Lean
counterpart is a discrepancy; default to "not faithful" if in doubt. Do NOT open the proof module
named below. OUTPUT: return ONLY a JSON object with keys "verdict" ("faithful" | "not faithful"),
"reason" (clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).

ROW lem:soft-rotation. Source: work/reviews/lem-soft-rotation-source-excerpt-lines-317-326.tex.txt (=
reference/SM/sm-5-transport.tex 317-326; proof 327-371 only for notation); def:soft and
lem:soft-generic at reference/SM/sm-2-amplitude.tex 996-1052 (sectors: same-sign χ_− = χ_+ = −τ_j,
mixed χ_− ≠ χ_+, loop χ_− = χ_+ = τ_j); sm-1-polygons.tex def:regular / lem:rot (rot). Statement:
work/reviews/lem-soft-rotation-reviewer-input-statement.lean.txt (main declaration SM.soft_rotation_law).
Definition modules: SoftInsertionTuple (softInsertion, SoftAdmissible, softAttachmentMinus/Plus),
work/lean/SM/SoftRotation.lean (openCone definition only), RotationNumber / RegularLocus /
PrincipalAngles (rotationNumber), Chirotope (turn), Generic, Polygon (edge). Do NOT open
work/lean/SM/SoftRotationLaw.lean. TASK: hypotheses (P generic, q admissible at j, "ε small
(lem:soft-generic)" as ∃ ε₀ > 0 ∀ 0 < ε < ε₀ with P_ε generic); conclusions rot(P_ε) = rot(P) in
same-sign and mixed sectors and rot(P_ε) = rot(P) − τ_j(P) in the loop sector (real identity with the
SignType cast); the three cone descriptions: same-sign sector = open cone strictly between ℓ_{j−1}
and ℓ_j, loop sector = open cone between −ℓ_{j−1} and −ℓ_j, mixed sector = complement of the closures
of both cones (is the Lean's "q ∉ closure(cone₁) ∧ q ∉ closure(cone₂)" that complement?).