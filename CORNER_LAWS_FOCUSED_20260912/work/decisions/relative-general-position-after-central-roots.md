# Full relative general position after actual central roots

Read STATUS.md for exact current build/review/audit status. Preserve every reviewed
SM module. The full thm:relgp and the wall-law/soft/unconditional R goal remain
pending; supporting lemmas do not increment the132 original proof denominator.

## Implemented central-root algebra and geometry

CentralLegPolynomial defines the actual parameter slope as the evaluated fixed
coordinate slope times the real scalar step. Its actual parameter polynomial has
constant equal to the initial hybrid control value. parameterPolynomial_eval
proves equality with actual multivariate evaluation along the coordinate leg.
Absent scalar variables give zero coordinate slope and a nonzero constant control.

CentralLegRootControls applies these identities to the actual finite named Δ/T
family. Every actual root forces genuine coordinate dependence, hence a nonzero
time slope; rootMultiplicity is1, HasDerivAt is the actual nonzero time derivative,
and every two parameters on opposite sides of the root have negative product of
control values. Distinct names cannot share a parameter root: both dependencies
are derived and the actual specialized resultant excludes their common moving
coordinate value. Roots cannot be at0 or1; each named factor has at most one root.

NonzeroControlsGeneric uses arbitrary-order ±coverage for area/concurrence
polynomials and the source's actual G1 remote interior-concurrence theorem. All
named controls nonzero implies actual Generic. The converse is intentionally
absent, since inactive T roots may be generic.

CentralLegFiniteRoots defines actual evaluation-zero root sets. They are finite,
have a unique vanishing control name, and are isolated. The finite set of pairs
(leg label,local parameter) retains the local occurrence information. Actual
nongeneric central times are only a SUBSET of these roots, hence finite. This is
not a declaration that every algebraic root is a wall event.

## Next local-root assembly

Prove a common neighbourhood of each root with all other control signs fixed.
Their evaluations are nonzero at the root by unique-name/no-common-root results,
and continuous by the actual parameter polynomial or HasDerivAt. For each other
control, its value times the value at the centre remains positive nearby; a finite
intersection gives one common neighbourhood. Combine with root isolation and the
Generic implication to obtain a punctured generic neighbourhood. At roots in(0,1),
shrink the radius to stay within this actual central leg. Inactive generic T roots
are omitted from wall events.

Inspect the actual WallGerm constructor and assemble centred continuous labelled
tuple germs from t↦tupleOfScalarCoordinates(leg.assignment W (r+t)). Retain the
actual centre and all labels. The root derivative is nonzero, but do not claim
ambient smooth-hypersurface structure merely from an univariate multiplicity
statement: use the nonzero actual fixed-coordinate slope and polynomial smoothness
to prove whatever ambient formulation is required. Named wall classification and
the T/crossing-parameter determinant identity remain separate unproved obligations.

## Scalar-box prototype for the global path

checks/ScalarBoxes.prototype.lean is outside the theorem library. Its current
successful root kernel run is10541, with six standard-only axiom traces. Read the
eventual independent prototype-review status in STATUS.md; no new original claim
is accepted by this prototype. Do not restart the mathematical construction.

It defines actual scalar open/closed boxes by componentwise absolute differences,
proves openness, closedness, closure inclusion, convexity, coordinate-hybrid and
affine-line containment, and positive-radius closed boxes inside any supplied open
neighbourhood. The actual tuple box is the preimage under scalarCoordinates.
exists_tupleScalarBox_closure_diameter gives closure inside an arbitrary actual
open tuple set S and STRICT Euclidean Metric.diam(tupleCoordinates''box)<δ,
plus pairwise distance<δ. The Euclidean bound uses a δ/4 radial neighbourhood,
so the true diameter is at mostδ/2<δ; pairwise strict<δ alone would be insufficient
to establish strict diameter. The product max metric is used only to choose a
topologically small scalar box, never equated with the Euclidean metric.

After independent review, port the exact prototype mathematical body into new
modules. Instantiate S with actual Regular; at the fixed endpoints use the open
intersection with Generic. This retains inactive endpoint T zeros correctly.

## Remaining global construction and full target

Construct a finite strict subdivision0=t0<...<tN=1,N≥3, subordinate to the cube
cover, with first and last cubes generic. Closed subinterval images must fit in
their actual cubes. Consecutive cubes then contain the same actual gamma(ti), so
their open overlap is nonempty. Choose internal waypoints in those overlaps using
the proved simultaneous joint-choice theorem; keep gamma(0),gamma(1) fixed.

Choose and prove a finite ordering/equivalence of the actual scalar label type
ZMod n×Fin2. Construct every ordered coordinate leg and concatenate them on the
actual subdivided time intervals. Prove hybrid and leg cube containment, actual
piecewise-affinity and continuity at every join, exact fixed labelled global
endpoints, regularity and the Euclidean uniform tolerance because gamma and the
new point share a cube at each time. Generic collars handle their own collision
freedom; central-leg collision freedom is already proved. Transfer root and sign
results through the actual increasing affine time rescalings, preserving labels.

Finally classify every nongeneric centre into exactly one actual F, V-bigon,
V-sliding, T, E or C wall, prove the relevant sign/order changes, handle inactive
T roots, exclude cusps using regularity, and finish complete occurrence tracking.
Only the whole source statement with independent semantic review may accept
thm:relgp. Continue the full main theorem and unconditional R thereafter.
