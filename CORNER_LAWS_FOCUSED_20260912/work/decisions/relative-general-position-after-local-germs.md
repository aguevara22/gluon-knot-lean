# Full relative general position after local germs and cubes

Read STATUS.md and checkpoint055 for the current build/review evidence. Preserve
all reviewed modules; full thm:relgp, the main wall laws, soft theorem and
unconditional R remain incomplete. No supporting lemma increments original claims.

## Local construction now available

ScalarBoxes is the exact mathematical body of the independently reviewed scalar
box prototype. RegularScalarBoxes constructs positive actual tuple cubes with
closures in Regular, or Regular∩Generic at a generic point, and strict actual
Euclidean diameter bounds. Endpoint inactive T zeros remain allowed. It also proves
hybrid endpoints and actual central legs stay in a cube containing both waypoints.

CentralRootNeighborhoods constructs one positive radius from the finite family of
continuous other-control products, root isolation, and the distances to 0 and 1.
CentralRootGerms constructs the actual source WallGerm on that radius. Its curve is
exactly the labelled tuple at original leg time r+t. Its centre, actual generic
puncture, collision freedom, other products, SignChanges and nonzero time derivative
are proved. The aggregate central_nongeneric_has_wallGerm derives a vanishing name
from actual nongenericness; it adds no root or transversality premise. Neither
ambient smoothness nor a named wall classification follows automatically.

OrderedCoordinateLegs chooses one genuine equivalence ScalarCoordinate n≃Fin(2*n),
defines all successive hybrids and scalar legs, and proves initial/final values,
consecutive joins, continuity and box containment. With two distinct internal
waypoint tags these legs equal the existing actual joint-waypoint assignment.
This is still an indexed collection of legs, not a global time-parametrized path.

## Next executable construction: strict finite subdivision with endpoint collars

Use the actual continuous γ:unitInterval→LabelledTuple n and its Regular hypothesis.
At each image point choose a positive cube as above. Choose separate generic cubes
at γ(0) and γ(1). The inverse image of each cube under γ is open in unitInterval.
These sets cover the interval because each central cube contains its centre.

Pinned Mathlib/Topology/UnitInterval.lean:469–486 provides a monotone eventually
constant subdivision from lebesgue_number_lemma_of_metric. Its statement alone
does not give the required strict finite partition, N≥3, or specified endpoint
cubes. A direct uniform mesh is preferable to silently treating that weaker result
as the full source subdivision:

1. Obtain a positive Lebesgue number for the cube preimages, and positive metric
   radii around 0 and 1 whose relative balls lie in the specified endpoint cubes.
2. Use exists_nat_one_div_lt (Algebra/Order/Archimedean/Basic.lean:214) and enlarge
   the mesh size to choose N≥3 with 1/N below all three positive radii. Prove the
   reciprocal inequalities explicitly when enlarging N.
3. Define t_j=j/N as actual unitInterval points for j:Fin(N+1). Prove t_0=0,
   t_N=1, strict monotonicity, and each cell length 1/N.
4. For each central closed cell, its points have distance ≤1/N from the left
   endpoint, hence lie in one cube's preimage by the Lebesgue number. Use the
   prescribed generic cubes for the first/last cells. Prove their containment
   from the corresponding endpoint distance bounds.
5. Consecutive cubes contain γ(t_j), so their actual tuple-space intersection is
   open and nonempty. Its scalar-coordinate image is open under the proved
   scalarCoordinateHomeomorph and contains the actual scalar image of γ(t_j).

The pure-Mathlib prototype checks/UniformMesh.prototype.lean now implements the
strict uniform mesh, fine N≥3 choice, both endpoint ball estimates and the full
abstract open-cover subdivision with prescribed first/last members. Root run73550
passed; consult STATUS.md and the prototype review before porting its frozen body.
This implements the abstract numerical/cover portion of steps1–4 above. Next apply
it to actual continuous-curve preimages of the chosen Regular/Generic tuple cubes;
retain all cube closure and Euclidean-diameter evidence when choosing cell members.

## Joint assignment and actual global path

Index the N−1 independent internal waypoints by Fin(N−1). Use the actual open
overlap domains. Central cells have both endpoints internal; their two tags are
the preceding/current internal waypoint indices, with distinctness proved by
their natural values. Index every central coordinate leg by its cell and
Fin(2*n), and instantiate orderedWaypointLeg with the fixed scalarCoordinateOrder.
The finite joint-choice theorem then supplies one assignment for all legs while
remaining in every actual open overlap. Keep the original two labelled endpoints
fixed; endpoint collars need only the proved generic box containment.

Concatenate the indexed coordinate legs on their actual subinterval times. Prove
the full continuous function and piecewise-affine property, with exact endpoint
and join identities. Every point must remain in its assigned cell's cube; then
the old and new values at the SAME time satisfy the Euclidean tolerance. Ordinary
Path.trans halves time at each join (Topology/Path.lean:275), so using it without
proved appropriate time rescaling does not establish this synchronous error bound.

For direct finite closed-cell gluing, pinned Mathlib/Topology/LocallyFinite.lean
has locallyFinite_of_finite at32 and LocallyFinite.continuous at111. The latter
proves continuity from an actual closed cover of the entire domain and continuity
on each member. Prove uniform-cell exhaustion and agreement on adjacent endpoints,
then define the selected local affine value and show it equals each branch on
that branch's cell. This avoids changing the source-time intervals. These gluing
and exhaustion lemmas are still to be proved; the API lookup alone is not evidence
of the global path construction.

Transfer local root finiteness, centred germs and nonzero derivatives through
the actual increasing affine time rescalings; retain all cell/leg/occurrence
labels. Prove collisions absent in central legs by the joint conditions, and in
generic collars by G1. Regularity and nonzero physical edges follow from the cube
closure containment, not just collision freedom.

## Full remaining mathematical obligations

Prove ambient smooth-hypersurface structure using the nonzero actual fixed-coordinate
slope and smooth polynomial coordinate functions (an explicit local graph is
available from the affine coordinate formula). Do not substitute multiplicity1 or
a nonzero time derivative for this ambient statement.

Complete the F/both-V/T/E/C dictionary, exhaustive/disjoint classification, the
regular n=3 collinear exclusion, strict middle-point betweenness for F, and cusp
exclusion. Prove the exact T/crossing-parameter identity and all required crossing
order exchanges. Inactive generic T roots are omitted from wall events. Complete
global occurrence tracking. Only a full source assembly and independent semantic
review may accept thm:relgp. Continue to the main laws, soft theorem and R afterward.
