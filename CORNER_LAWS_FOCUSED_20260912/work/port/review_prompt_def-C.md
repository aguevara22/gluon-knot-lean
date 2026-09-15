You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE definition row against ONE printed source definition (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/def-C-source-excerpt-lines-1688-1700.tex.txt (= reference/SM/
   sm-3-statesum.tex 1688-1700, def:C). Context, read ONLY to fix notation: reference/SM/sm-3-statesum.tex
   242-260 (def:uniform: m_Q, r_Q, uniform supports), 325-351 (def:positive-lift: the positive lift of a
   subpolygon, its writhe m_Q), 1787-1800 (lem:C-X1, a consumer), 9-60 (def:decomposition, def:smoothing,
   conv:selected-visits, lem:carriers: decompositions S ∈ Ind(G_P) and their subpolygons Q); reference/SM/
   sm-1-polygons.tex 63-72 (def:chirotope: ℓ(P) = #{i : τ_i(P) = 1}, the number of left turns), 240-268
   (def:gauss, def:interlace: Ind(G_P)); 916-923 (lit:homfly: H ∈ ℤ[a^{±1}, z^{±1}]).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/def-C-reviewer-input-statement.lean.txt
   (module SM/CornerStateSum.lean: the DEFINITIONS carrierRotationInt, cornerSlot, cornerHomfly,
   cornerCoefficientWith, cornerCoefficient, uniformDecompositions, cornerProduct, cornerStateSum with their
   supporting lemmas (proofs not under review), the bundle `CornerStateSumDefinitionData` and the main
   declaration `SM.corner_state_sum_definition`). Its module docstring maps notation — verify it, do not trust it.
   Do NOT open work/lean/SM/CornerStateSum.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review), all ACCEPTED rows unless
   noted: work/lean/SM/UniformDefinition.lean (carrierRotation, CarrierUniform, UniformDecomposition — def:uniform),
   DecompositionDefinition.lean (IsDecomposition — def:decomposition), InterlaceSupports.lean (independentSupports
   = Ind(G_P)), CarrierSmoothing.lean (Carrier.Component = the subpolygons of S), CarrierCrossings.lean
   (carrierCrossingCount = m_Q), CarrierCornerPolygon.lean (ccpCornerPolygon, the corner polygon of a subpolygon;
   ccpCornerPolygon_regular statement), RotationNumber.lean (rotationNumber, rotationNumber_integer statement),
   Chirotope.lean (leftTurns, turn), PositiveLiftDefinition.lean and LinkPositiveLift.lean (positiveLift,
   positiveLift_isPositive, positiveLift_writhe_eq_carrierCrossingCount statements — def:positive-lift),
   LinkInterfaces.lean (homfly = the map of lit:homfly), LinkLaurentRing.lean (R, coeffAt d k f = the coefficient
   of a^d z^k, coeffAt_eq_zero_of_notMem_support / mem_support_iff_coeffAt_ne_zero statements), LinkDiagram.lean
   (Diagram, writhe, IsPositive).

YOUR TASK: decide whether the definitions + bundle pin down exactly the printed def:C. Check each printed
piece: (a) "For a subpolygon Q of a decomposition of the generic polygon P" — `q : Component hn hP S` with
`hS : IsDecomposition hn hP S` (S ∈ Ind(G_P)), P generic with n ≥ 3; (b) "H⁺_Q the HOMFLY–PT polynomial of its
positive lift" — `cornerHomfly := homfly (positiveLift …)`; (c) "d_Q = 1 − m_Q − |r_Q|" — `cornerSlot :=
1 − carrierCrossingCount − |carrierRotationInt|` where `carrierRotationInt := round (carrierRotation …)` is the
integer value of the real rotation r_Q (the accepted carrierRotation is real-valued; the bundle records
that on decompositions it is an integer and that the cast of cornerSlot equals the printed real formula) —
is this integer device faithful, and is it harmless that `round` gives a value also off decompositions where
the printed d_Q is undefined?; (d) "c(Q) = [a^{d_Q} z^0] H⁺_Q ∈ ℤ, the coefficient of a^{d_Q} z^0 (zero if that
monomial is absent)" — `cornerCoefficient := coeffAt (cornerSlot …) 0 (cornerHomfly …)` with the absence clause;
(e) "C(P) = (−1)^{ℓ(P)} Σ_{S ∈ Ind(G_P), S uniform} (−1)^{|S|} ∏_{Q subpolygon of S} c(Q)" — `cornerStateSum`
summing over `(uniformDecompositions hn hP).attach` (Ind filtered by UniformDecomposition, the membership proof
threaded to the positive lift), the sign (−1)^{S.card}, the product over the Fintype `Component hn hP S`, the
global sign with `leftTurns P` (= ℓ(P) of def:chirotope?); is `UniformDecomposition` exactly "S uniform" of
def:uniform; are the two displayed forms of state_sum (attach over uniform sets / dite over all of Ind)
equal to the printed formula; does the bundle contain any clause without a printed counterpart or miss any
printed clause? Expand definitions to primitives; say where the Lean is STRONGER or WEAKER. Default to "not
faithful" if in doubt; label non-blocking discrepancies "non-blocking" in their text.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
