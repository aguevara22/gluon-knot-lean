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

ROW lem:star-generic. Source: work/reviews/lem-star-generic-source-excerpt-lines-16-33.tex.txt (=
reference/SM/sm-5-transport.tex 16-33; proof 34-70 only for notation; def:star at 5-14). Notation:
sm-1-polygons.tex def:polygon, def:chirotope (χ, τ), def:generic, def:regular and lem:rot (principal
turns, rot), def:crossings (X(P)), def:shift; sm-0-legend.tex. Statement: work/reviews/lem-star-generic-reviewer-input-statement.lean.txt
(main declaration SM.star_generic_law). Definition modules: work/lean/SM/StarPolygons.lean (unitPoint,
star, starNeg, starAngle, starRadius, rotationMap — definitions and lemma STATEMENTS only),
work/lean/SM/BowTie.lean (bowTie), Chirotope (chi, turn, strictlyLeft), RegularLocus / PrincipalAngles /
RotationNumber (principalTurn, rotationNumber), Generic, Crossings (crossingSet), EuclideanPlane
(euclideanLength, planeDot), Polygon (edge, edgePoint). Do NOT open work/lean/SM/StarGenericLaw.lean.
TASK: check gcd(r,N)=1; (i) σK_r = R(K_r) with R the rotation by 2πr/N (is rotationMap that rotation,
and is shift 1 = σ), every principal turn = 2πr/N ∈ (0,π), all turns left (turn = 1), rot(K_r) = r;
(ii) every edge line tangent to the circle of radius ρ = cos(πr/N) about the origin at the edge
midpoint (the Lean states: midpoint norm = ρ, edge ⟂ midpoint, other points of the line farther —
is this the printed tangency?), origin strictly left of every directed edge; (iii) K_r generic,
K_{−r} generic, all turns right, rot = −r; (iv) K_0 generic with the printed chirotope values, turns,
rot 0 and X(K_0) = {{1,3}} (labels: source 4 = residue 0).