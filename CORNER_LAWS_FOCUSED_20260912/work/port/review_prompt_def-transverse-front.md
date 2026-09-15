You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE definition row against ONE printed source definition (frame SM15):
def:transverse-front (row 92), Lean declaration `SM.transverse_front_definition : SM.TransverseFrontDefinitionData`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/def-transverse-front-source-excerpt-lines-3328-3339.tex.txt (= reference/SM/sm-3-statesum.tex
   3328-3339). Context, ONLY to fix notation: sm-3:3340-3403 (the literature block src:contact: the contact conventions, the
   front and pushoff inputs — a PENDING interface, not part of this row), 3404-3430 (fd:contact, the consumer: which objects of
   the definition it names — the front, D_T, its writhe, the knot T), 1825-1841 (ng:front-domain: the smooth-curve vocabulary,
   s(F), over = smaller dz/dx for LEGENDRIAN fronts — note the difference with this row's rule "smaller y"), the display
   fd:front-writhe if it exists (grep 'front-writhe' in sm-3), 325-351 (def:positive-lift: writhe as the sum of crossing signs
   σ(c) = sgn det(u_O, u_U)), reference/SM/sm-1-polygons.tex 240-268 (def:gauss: occurrences, over/under bits).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/def-transverse-front-reviewer-input-statement.lean.txt
   (module SM/TransverseFront.lean: the definitions Space, contactForm, xOf/yOf/zOf, xzOf, SameT, TransverseKnot,
   SmoothKnotDiagram (loop, vel, IsDouble, doubleSet, isOver, crossingPairs, crossSign, writhe, occSet, overOcc, underOcc,
   overCount, underCount, crossingCount), TransverseKnot.front, IsGenericPositiveTransverseFront, the bundle
   TransverseFrontDefinitionData and theorem SM.transverse_front_definition are UNDER REVIEW; helper lemmas' proofs are not).
   Its module docstring maps the printed notation and lists the readings T-1..T-5 — verify them, do not trust them. Do NOT open
   work/lean/SM/TransverseFront.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/FrontSmooth.lean (SmoothLoop,
   Param, SameParam, SmoothFront, IsCusp, vel, slope, crossSign — the accepted ng:front-domain vocabulary), SM/FrontRecordBridge.lean
   §1 (IsDoubleOf, occSetOf, slopeOf, crossSignOf for loop families), SM/EuclideanPlane.lean (det), SM/LinkDiagram.lean (sign,
   writhe of polygonal diagrams — for comparison only). You MAY read work/AUTHOR_NOTES.md entries "FR-1..FR-7", "D-F1..D-F5" and
   the GAP-1/GAP-2 scope entries (2026-09-14) for the recorded readings of the front block.

READINGS DISCLOSED BY THE UNIT (judge each): T-1 smooth = C^∞, the parameter circle = a 1-periodic map of ℝ (FR-3), oriented =
the parameter direction, embedded = injective on the circle; T-2 over = smaller y as a relation IsDouble s t ∧ y s < y t on
parameters, well defined by embeddedness; T-3 "no cusp" = vel ≠ 0 (the negated accepted cusp criterion); T-4 "over/under counts"
= the tallies of over- and under-passages along the traversal (each equal to the crossing number, partitioning the occurrence
set); T-5 "the diagram determines its writhe and its over/under counts" = the quantities are functions of the diagram alone, and
the front of T depends on T only through the projection and the y-order at double points (front_ext). Risk R-1: the printed
"immersion" clause is implied by positivity but kept as a field. Risk R-3 (not this row): the polygonal reading of transverse
fronts for fd:contact is not built here.

YOUR TASK: decide whether the definitions + bundle pin down exactly the printed definition. Sentence by sentence: "In (ℝ³,
ker(dz − y dx))" (contact_space: is the contact form α = dz − y dx rendered, and is the field a definition or an assertion?); "a
generic positive transverse front is the oriented knot diagram in the (x,z) plane obtained from a smooth oriented embedded knot T
with z′ − y x′ > 0" (knot, positive, knot_named: is `TransverseKnot` exactly that class — nothing added (e.g. the immersion
of T, the projection conditions) beyond the printed clauses, nothing missing; is IsGenericPositiveTransverseFront D ↔ ∃ K, K.front = D
the printed "obtained from"?); "whose xz projection is an immersion of the parameter circle with finitely many transverse
double points and no triple point" (projection, double_points, no_triple: transversality as det ≠ 0 of the projected velocities;
finiteness via doubleSet; no triple point as printed); "the over strand at each double point being the branch of smaller y"
(over_rule); "It has no cusp" (no_cusp — consequence or clause?); "At a vertical tangent, x′ = 0, the inequality gives z′ > 0: every
vertical tangent … points upward, a consequence and not a hypothesis" (vertical_up — proved, as printed); "The diagram determines
its writhe and its over/under counts; the knot T is named separately where it is used" (writhe_counts, determined, knot_named:
is the writhe the printed one — sum over double points of sgn det(u_over, u_under) with over = smaller y; is the reading of
"over/under counts" defensible from the frozen text, or is it an invention that must be flagged; is "determines" rendered
faithfully). Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; any printed clause without a Lean
counterpart or Lean clause without a printed counterpart is a discrepancy (label non-blocking ones). Default to "not faithful"
if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
