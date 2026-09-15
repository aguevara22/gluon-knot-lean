You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma row of the CV lane against ONE printed source statement of the
paper "CV" (reference/R/CV/d3_floor.tex, frozen).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-uniformrot-source-excerpt-lines-263-302.tex.txt (= reference/R/CV/
   d3_floor.tex 263-302: CV:lem:uniformrot, statement 263-276 and its printed proof 277-302 — the proof only to fix the
   meaning of "principal turns exist", "Π the sum of the positive ones", and the remark at 283-288 that the hypothesis
   of (ii) "names one negative turn and admits turns equal to zero, which Π omits"). Context, ONLY to fix notation:
   reference/R/CV/d1_setup.tex 22-40 (CV def:regular: principal turns exist), 820-905 (CV def:rot and lem:turnlift —
   grep `label{def:rot}` and `label{lem:turnlift}` for the exact lines), and the CV excerpts of the accepted rows
   work/reviews/cv-def-regular-source-excerpt-*.tex.txt, work/reviews/cv-def-rot-source-excerpt-*.tex.txt,
   work/reviews/cv-turnlift-source-excerpt-*.tex.txt (if present; `ls work/reviews | grep cv-`).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/cv-uniformrot-reviewer-input-statement.lean.txt
   (module CV/UniformRot.lean: module docstring with the notation map — verify it, do not trust it; helper lemmas
   with proofs NOT under review; the bundle `CV.UniformRotData` and the theorem `CV.uniformrot` at the END). Do NOT
   open work/lean/CV/UniformRot.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/Setup.lean (CV.IsPolygon,
   CV.Regular, CV.principalTurn and their `_iff_sm` / `_eq_sm` bridges to SM), CV/Rotation.lean (the accepted CV:def:rot:
   `CV.rot L hL : ℤ`, rotRay, Admissible, `two_pi_mul_rot` / `turnlift_ii` statements, `rot_eq_rotationNumber`,
   `rot_reversal` statement), CV/RotationSmooth.lean (the accepted CV:def:rot bundle — statement only), work/lean/SM/
   Regular*.lean (SM.Regular, principalTurn, principalAngle, principalAngle_bounds — definitions), SM/Chirotope.lean (turn),
   SM/Polygon.lean (LabelledTuple, edge).

YOUR TASK: decide whether the bundle pins down exactly the printed lemma. (i) "Let L be a closed polygon all of whose
principal turns exist and are positive. Then rot(L) ≥ 1, with equality if L has three corners. If all turns are negative,
rot(L) ≤ −1, again with equality in absolute value for three corners": fields pos_ge_one, pos_three, neg_le_neg_one,
neg_three — is `L : LabelledTuple c` with `hL : Regular L` the printed "closed polygon all of whose principal turns
exist" (CV def:regular), is `0 < principalTurn L i` "positive", is `c = 3` "L has three corners", is `rot L hL = -1`
the printed "equality in absolute value" in the negative case, and is `CV.rot` the printed rot of def:rot? (ii)
"exactly one negative principal turn, of magnitude α ∈ (0, π), and let Π be the sum of the positive ones. Then Π − α =
2π r with r = rot(L) an integer, and r ≥ 1": field one_dissent — an index a with `principalTurn L a < 0` and
`∀ i ≠ a, 0 ≤ principalTurn L i` (zero turns admitted, as the printed remark 283-288 says — is "exactly one negative"
rendered exactly?), α = −principalTurn L a (the docstring says 0 < α < π is automatic for a principal turn — is
dropping it as a hypothesis faithful?), Π = the sum over `Finset.univ.erase a` (equal to the sum of the positive turns
since zero turns contribute nothing — is that the printed Π?), conclusion `… − α = 2 * π * rot L hL ∧ 1 ≤ rot L hL`
("r = rot(L) an integer" is the type ℤ). Expand definitions to primitives; say where the Lean is STRONGER or WEAKER
(e.g. an extra hypothesis, or a conclusion holding without the sign hypothesis); default to "not faithful" if in doubt;
label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
