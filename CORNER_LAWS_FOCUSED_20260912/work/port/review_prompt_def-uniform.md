You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE definition row against ONE printed source definition (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/def-uniform-source-excerpt-lines-242-248.tex.txt
   (= reference/SM/sm-3-statesum.tex 242-248, def:uniform). Context, read ONLY to fix notation:
   reference/SM/sm-3-statesum.tex 1-52 (def:decomposition, def:smoothing — subpolygons = carriers,
   their corners, their crossings and m_Q — and conv:selected-visits; all accepted rows) and 54-95
   (lem:carriers, accepted: in particular clause (ii), every carrier read at its corners is a
   regular polygon with at least three corners and nonzero turns); reference/SM/sm-1-polygons.tex
   63-71 (def:chirotope: turns τ_i ∈ {-1, 0, 1}, left turns = #{i : τ_i = 1}), 386-397 (def:regular)
   and 407-421 (lem:rot: rot(P) = (1/2π) Σ ϑ_i(P) on the regular locus).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/def-uniform-reviewer-input-statement.lean.txt (definitions CarrierUniform,
   CarrierMixed, UniformDecomposition, carrierRotation, carrierLeftTurns; bundle
   UniformDefinitionData; main declaration SM.uniform_definition). Its module docstring maps
   notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): CarrierCornerPolygon (ccpCornerList, ccpCornerCount, ccpCornerMark,
   ccpCornerPolygon — definitions only; the statement of carriers_clause_ii), CarrierCrossings
   (carrierCrossings, carrierCrossingCount), CarrierSmoothing (Component, owner, smoothingSuccessor),
   CarrierTrueCorners (IsTrueCorner), SmoothingDefinition and CarriersLemma (accepted rows
   def:smoothing and lem:carriers — statements only), DecompositionDefinition (IsDecomposition),
   Chirotope (chi, turn, leftTurns; accepted row def:chirotope), RegularLocus (Regular,
   principalTurn), RotationNumber (rotationNumber), RotationTheorem (accepted row lem:rot — statement
   only), Polygon (LabelledTuple, edge). Do NOT open work/lean/SM/UniformDefinition.lean (it
   contains the proof; the statement file reproduces everything else in it).

YOUR TASK: decide whether the Lean definitions, as pinned down by the bundle
UniformDefinitionData, define exactly the printed notions. Check: (a) "A subpolygon Q is uniform if
all its turns have one sign and mixed otherwise" — the subpolygon Q is a carrier q : Component of a
smoothing and its turns are read on its corner polygon ccpCornerPolygon (the carrier at its corners
in inherited order, lem:carriers (ii)); is that the printed subpolygon and are "its turns" the
turns at its corners? Is "one sign" rendered by ∃ τ ≠ 0, ∀ j, turn … = τ (does the extra τ ≠ 0
change anything given lem:carriers (ii), and is a subpolygon with a zero turn excluded as printed)?
(b) "A decomposition S is uniform if all its subpolygons are" (UniformDecomposition: ∀ q). (c)
"r_Q = rot(Q) (lem:rot, applicable by lem:carriers)": carrierRotation = rotationNumber of the corner
polygon, with the regular_carrier clause certifying applicability — is the rotation number of the
corner polygon the printed rot(Q) (compare with def:regular / lem:rot; the corner polygon has the
same traced curve as the carrier by lem:carriers (ii))? (d) "m_Q for its number of crossings":
carrierCrossingCount = card of carrierCrossings (def:smoothing's crossings of Q). (e) "ℓ_Q for its
number of left turns": carrierLeftTurns = leftTurns of the corner polygon = #{j : turn = 1}; is a
left turn τ = +1 as in def:chirotope? Domain: the definitions are stated for any S : Finset
(Crossing P) with P generic and n ≥ 3, while the source speaks of decompositions; say whether the
wider domain is harmless. Expand definitions to primitives; say where the Lean is STRONGER or
WEAKER; any printed notion without a Lean counterpart, or any Lean clause without a printed
counterpart, is a discrepancy. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
