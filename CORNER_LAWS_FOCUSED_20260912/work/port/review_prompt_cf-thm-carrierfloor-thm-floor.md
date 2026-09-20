You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statements
you are reviewing and you must not read their proofs. Your job is a statement-fidelity review of ONE row against ONE
printed source statement (frame SM15); the row is named in your task: either cf:thm-carrierfloor (row 99, Lean
declaration `SM.cf_thm_carrierfloor : SM.CarrierFloorData`) or thm:floor (row 100, `SM.thm_floor : SM.FloorTheoremData`),
both in module SM/CarrierFloorRows.lean with their statement bundles in SM/CarrierFloor.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: row 99 — work/reviews/cf-thm-carrierfloor-source-excerpt-lines-4282-4339.tex.txt
   (= reference/SM/sm-3-statesum.tex 4282-4339, Theorem cf:thm-carrierfloor, clauses (R), (A), (B), (C)); row 100 —
   work/reviews/thm-floor-source-excerpt-lines-4576-4585.tex.txt (= sm-3:4576-4585, Theorem thm:floor). Context ONLY to
   fix notation: sm-3:4340-4575 (the proof of row 99 — which objects it uses: the rounding record, the tangency count,
   the transverse lift, the mirror D̄, fd:contact), 4586-4602 (proof of row 100), cf:lem-rounding (grep "cf:lem-rounding"
   for its statement), cf:def-turning (4300 region, "direction loops and smooth rotation"), lem:rot, lem:uniformrot,
   def:C (grep "def:C" — cornerHomfly / d_Q / m_Q / r_Q), lem:carriers, rem:rounding-record and rem:curlauthor (grep).
2. The Lean statements: work/reviews/cf-thm-carrierfloor-thm-floor-reviewer-input-statement.lean.txt (the row module,
   proofs withheld) and work/reviews/carrier-floor-statements-reviewer-input.lean.txt (= SM/CarrierFloor.lean with every
   proof replaced by sorry; UNDER REVIEW are §1 (TransverseKnot.Reads, TransverseFrontBound — the row-94 interface, now
   discharged), §2 CarrierFloorRData, §3 Round / junctionTemplate / CarrierFloorAData, §4 AllPosOrOneNeg /
   UniformOrOneDissent / tangencySet / CrossesPositively / TangencyCount / BClaim / CarrierFloorBData, §5 CarrierFloorCHyp /
   zZeroPart / CarrierFloorCData, §6 CarrierFloorData, §7 AllLeftOrOneRight / CarrierUniformOrOneDissent /
   FloorTheoremData; §8 (the proof-route helper statements, prefixed ur_/ua_/ub*/ui_/usw_/ucurl_/urot_/ul*/uf_/ueq_) and
   §9 are NOT under review — use them only to confirm that no hypothesis is smuggled into the row theorems). Docstrings
   quote the source — verify them, do not trust them.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/Rounding.lean
   (cf:lem-rounding: RoundingWitness, Carried, PolygonDiagram, CornerRounding.roundedWitness / clearance / Admissible /
   juncArc / uDir / vDir — grep), SM/Curl.lean (RecordCarried — definitions only), SM/TurningNumber.lean + SM/TurnLift.lean
   (ClosedC1Curve, rot, reverse), SM/RotationNumber.lean (rotationNumber, principalTurn, Regular), SM/RotationReversal.lean,
   SM/UniformRotation.lean (the statement of uniform_rotation), SM/LinkDiagram.lean + SM/LinkDiagramRecord.lean +
   SM/LinkMoves.lean (Diagram, reverse, sign, writhe, IsPositive, Shadow.single, generic, componentCount, LinkEquiv —
   grep), SM/PolynomialBlock.lean, SM/LocalPolynomial.lean (P), SM/LinkLaurentRing.lean (coeffAt, degAZ, mindegAZ,
   mindegZZ, InSupportM), SM/AdegDefinition.lean, SM/CornerStateSum.lean (def:C: cornerHomfly, cornerSlot,
   carrierCrossingCount, carrierRotationInt, carrierRotation, CarrierUniform, ccpCornerPolygon, turn, IsDecomposition,
   Component), SM/CarrierCornerPolygon.lean, SM/LinkPositiveLift.lean, SM/TransverseFront.lean (TransverseKnot, front,
   writhe), SM/CeSmoothingRecord.lean (SpatialLink.HeightMarking), SM/SrcContact.lean (TransverseKnot.spatial), and Mathlib.
4. Disclosed readings: work/AUTHOR_NOTES.md entries of 2026-09-15 "Floor lane (rows 99 cf:thm-carrierfloor, 100 thm:floor):
   design panel judged …" (decisions D-FL-1..3 and the fidelity risks FR-FL-R1..R3, A1..A2, B1..B5, C1..C9, F1..F3),
   "Floor lane wave 1 …" (D-FL-4: the internal MirrorSubstitutionData.coeff repair — a proof-route structure, not a row
   statement) and the port entry.

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing
SM.CarrierFloorRows if you wish — the machine is loaded, batch your checks): both row theorems have no hypothesis;
axioms exactly [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm,
SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact] — all registered literature interfaces (row 99 (C) consumes
fd:contact, which consumes src:contact, lit:homfly and, through row 91, the second declaration of lit:homfly).

YOUR TASK — row 99: compare each printed clause with its bundle. (R) "Let D be an oriented knot diagram and −D … Then
P_{−D} = P_D; consequently an oriented knot and its reverse have the same polynomial. Moreover −D has the same crossing
signs and the same writhe as D, and the rotation of its underlying plane curve is the negative of that of D" (with the
scoping sentence on rot) ↔ CarrierFloorRData (knot-case P_reverse, knot_reverse via LinkEquiv, sign_reverse,
writhe_reverse, the polygon and C¹ rotation reversal); (A) "the construction … returns one curve and one diagram at those
data: the junction inserted at the corner q_i is determined by ε, by the two incident unit directions and by the
transition profile … the arc length ℓ is then determined by the endpoint condition, and the rest of the curve is L
itself. Write Round(L,D,ε) = (L_ε, D_ε)" ↔ Round := CornerRounding.roundedWitness, junctionTemplate, CarrierFloorAData
(one_record, diagram_eq, junction_determined — parametric, FR-FL-A1 —, length_determined, rest_is_L); (B) "Let L be a
closed polygon with nonzero edges and nonzero principal turns, finitely many transverse double points, no triple points, no
corner at a double point and no corner on a non-incident edge, carrying a diagram D. Assume, after reversing orientation
if necessary, that either all principal turns are positive, or exactly one is negative and all others are positive. Put R
= |rot(L)|. Then there are a direction u ∈ S¹ and an ε₁ > 0 such that for every ε ∈ (0, ε₁) the rounded curve L_ε of the
record Round(L,D,ε) has exactly R points at which its unit tangent equals u and exactly R at which it equals −u; at each
of them the tangent crosses that direction in the positive sense" ↔ UniformOrOneDissent, BClaim, tangencySet,
CrossesPositively, TangencyCount, CarrierFloorBData — judge FR-FL-B1 (the claim asserted for the NORMALISED orientation:
for L itself, or for −L carrying −D — the literal reading for the record of L itself is false for an all-negative L; is
this faithful to "after reversing orientation if necessary"?), FR-FL-B2..B5; (C) "Let D be an oriented knot diagram all of
whose crossings are positive, with writhe w, whose underlying plane curve is a closed polygon L with all principal turns
existing, nonzero, and of magnitude below π, with finitely many double points, all transversal, with no triple points, none
of them a corner of L, and no corner of L lying on a non-incident edge; and let R be the absolute value of its Whitney
rotation number. … Assume that, after reversing the orientation if necessary … either every principal turn is positive,
or exactly one is negative and every other is positive. Then min deg_a P_D(a,z) ≥ 1 − w − R, and the same bound holds for
f_D(a) = [z⁰]P_D(a,z) whenever f_D ≠ 0" ↔ CarrierFloorCHyp (7 fields incl. the redundant printed ones, FR-FL-C1),
CarrierFloorCData (floor in mindegAZ over ℝ with |rotationNumber|; floor_zZero via zZeroPart, FR-FL-C3); the parenthetical
proof remarks (FR-FL-C5) and rem:curlauthor as commentary. Row 100: "Let Q be a subpolygon of a decomposition of a generic
polygon, and suppose that after possibly reversing its orientation either all turns are left, or exactly one turn is
right. Then min deg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q, H⁺_Q ∈ ℤ[a^{±1}, z²], so min deg_z H⁺_Q ≥ 0" ↔ AllLeftOrOneRight,
CarrierUniformOrOneDissent (literal reversal form, FR-FL-F1), FloorTheoremData (a_floor in ℤ and ℝ on def:C's cornerSlot /
cornerHomfly / carrierCrossingCount / carrierRotation, z_parity via InSupportM 1 and mindegZZ, FR-FL-F2/F3). Expand
definitions to primitives. Say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful"
if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite
source and statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of
strings), "supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
