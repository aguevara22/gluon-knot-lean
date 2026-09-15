# Completed: wall-segment stability

Completed on 2026-09-10 in SM/SegmentStability.lean and
SM/WallSegmentStability.lean. SM.wall_segment_stability compiles and has an
independent faithful review in reviews/lem-wall-segment-stability.json.
The compact-projection route below was implemented, followed by actual unique
transverse intersection, both parameter continuities on a common open U, and
simultaneous finite-family order preservation. Retained notes below describe
the original plan, not remaining requirements of this accepted claim.

The existing ContinuousGeometry helpers prove local parameter continuity,
strict parameter-bound/order persistence and the transverse-intersection branch.
They are not a proof of the entire source lemma and are not counted separately.

Suggested next route for the disjoint branch (UNPROVED PLAN): consider the space
of four real-plane endpoint/direction vectors. Closed-segment intersection is
the existence of two parameters in the compact square [0,1] × [0,1] satisfying
an actual vector equality. The equality relation is closed by continuity.
Projecting away the compact parameter square preserves closedness. Hence the
nonintersection configurations form an open set. Pull this open neighborhood
back through the endpoint/direction functions continuous at the centre. This
avoids incorrectly imposing global continuity when the source requires only
local variation. Mathlib's compact unit-interval subtype and closed projection
lemmas should support this argument. Check actual APIs locally.

For continuity of parameters at nearby times, retain the source's continuously
varying local domain; continuity merely at the centre proves continuity there,
not automatically throughout a neighborhood. Combine the coordinate continuity
lemmas pointwise on the supplied open local domain with eventual nonzero
intersection determinant. Finite intersection of neighborhoods handles all
segment pairs and every ordered pair of crossing parameters. Include the empty
family without a hidden nonemptiness hypothesis.

The plane representation is the actual product of two real coordinates. Its
product topology is the usual topology on R². If using norm or metric lemmas,
remember the default product norm is a max norm, not the later Euclidean norm
used for turning angles; do not silently identify their numerical norms. The
topological closed-projection route needs no such norm identification.

## Completed next step: generic-locus openness and chambers

The route below was completed in GenericTopology.lean. The full def:chamber and
prop:chambers were subsequently proved and independently accepted in
CyclicChambers.lean and ChamberPaths.lean. The next active plan is now
weak-openness-next.md. The remaining text is the historical proof plan.

Continue toward all clauses of prop:chambers and def:chamber, without counting
their partial helpers as original proofs. Prove G1 open by continuity of every
nonzero determinant and finite intersection. For G2, one possible route is:

1. Show that under G1, common interiors of distinct edges imply remoteness,
   using g1_adjacent_intersection and edgePoint_injective at the shared vertex.
2. Thus G2 under G1 is equivalent to absence of a common point of three
   pairwise remote closed segments. The reverse implication uses
   g1_remote_meeting to put their common point in all three interiors.
3. For each fixed triple, actual closed-segment common-point configurations
   form a closed set: project the closed equality locus over [0,1]^3. This is
   the same compact-projection construction now proved for pairs, with two
   equality conditions on a compact parameter cube.
4. Combine the finite triple complements and the open G1 set to prove Generic
   open. Then implement the actual cyclic quotient topology and connected
   components, and prove all remaining chamber/path-invariance clauses.

This route is a proof plan, not accepted mathematics. The source's own
crossing-point-separation proof is also available. Both must preserve the actual
geometric genericity and connected-component definition; do not replace the
chamber by a mere chirotope equivalence class.
