# Next candidate proof: thm:A-S3

Source: reference/SM/sm-2-amplitude.tex:380–461. This is the flat deletion law
for every physical root. It is a dependency toward the final corner laws, not
the final corner theorem. Keep the accepted definitions, axioms, map and canonical
modules unchanged while preparing candidates. The assembled single-triple
candidate remains subject to stronger fidelity review.

Start with the physical deletion-root map in source def:induced-roots. Existing
DeletionIndices and DeletionHalvesDefinition give the exact deletion vertex map,
its omitted/exhaustive labels, inherited edges and fused edge. State and prove
which deletion root has the same physical endpoints as each surviving old edge;
both incident roots must map to the fused edge. Do not substitute a root-slot
number without the endpoint proof. Using input arity n+1 matches deleteVertex.

Then specialize the response in three exhaustive root cases:

1. Nonincident root: the boundary order of the critical points is predecessor,
   deleted vertex, successor. Prove consecutive boundary positions, two formal
   singleton gaps, positive epsilons, and properness from input arity at least
   four. Identify the actual contracted word with the actual deleted polygon
   through its explicit cyclic relabelling. Use treeCoefficient_shift only after
   proving the tuple and physical-root correspondence.
2. Root on the incoming incident edge: the critical order is deleted vertex,
   successor, predecessor, and the span is full. The first gap is singleton;
   the other is the deletion word, rooted at the fused edge. Strict betweenness
   gives the epsilon pair minus one, plus one. The unit nonleaf value vanishes;
   the remaining barred gap output is the deletion tree coefficient.
3. Root on the outgoing incident edge: the critical order is successor,
   predecessor, deleted vertex. The span is full; reverse which gap is singleton.
   The epsilon pair is plus one, minus one. Again retain the exact deletion word
   and fused physical root when identifying its barred gap output.

On both sides, the reverse-ordered critical far sign is the negative of turn at
the deleted vertex: the critical boundary order is a cyclic permutation of the
three consecutive vertices. Combine chi_cyclic/chi_swap_outer with turn_det to
prove this. The source's right side has turn minus one; its left side has turn
plus one. Account for the subtraction order explicitly when applying the signed
response. Do not infer this sign from the names positive/negative time.

Useful existing inputs: WallGerm.FlatAt, flat_wall_sides, g1_deleteVertex,
deletion_data, treeCoefficient_shift, farOnly_leaf_values,
farOnly_nonleaf_E, critical_closed_gaps_G1, restricted-word far-output/tree
identification, and the frozen SingleTripleTreeResponse prototype. Inspect exact
types before using them. The new root map and all three branch specializations
need their own technical review; no current source claim is accepted by this note.
