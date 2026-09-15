# Full relative general position after polynomial controls

Target: the complete original thm:relgp, reference/SM/sm-1-polygons.tex:1385–1558.
Preserve the full corner state-sum wall-law, soft-theorem and unconditional R
goal. The transport-polynomials source row requires final independent acceptance;
read STATUS.md for its actual current state. A successful build alone is not
source acceptance. Keep all reviewed source modules unchanged and add new modules.

## Exact requirements

For every continuous path in the actual regular locus with generic endpoints
and every positive tolerance, construct a piecewise-affine path with exactly
the same labelled endpoints, uniformly within the tolerance, still regular,
collision-free and with finitely many isolated nongeneric parameters. Each must
give exactly one actual simple transversal named wall germ: F, either V branch,
T, E or C. Exclude cusps. Preserve all occurrence labels and distinguish inactive
zeros of concurrence polynomials from actual nongeneric events.

Do not assume endpoint concurrence polynomials are nonzero: a generic endpoint
can have concurrent supporting line extensions outside the actual segments.
Do not equate all polynomial zeros with wall events. Do not use an abstract
general-position or transversality axiom.

## Existing proved components

- GenericTopology and the accepted chamber work prove openness of the actual
  Generic locus using finite segment/crossing stability. RegularPerturbation
  exports isOpen_Regular for the actual nonzero-edge/non-antiparallel domain.
- TransportPolynomials supplies the finite named Δ/T family, exact geometric
  evaluation, nonzero irreducibility/nonassociation, affinity, formal slopes,
  resultants and specialized root tests. Coverage of arbitrary orderings is
  proved up to sign. Use its true source-facing fields, not unproved hypotheses.
- PolynomialAvoidance proves density from actual polynomial restrictions to
  tuple lines and a nonzero witness, plus a finite-family version. Generalize to
  arbitrary finite scalar assignment spaces when joint waypoint variables are
  needed; do not treat an unproved surjectivity assertion as a witness.
- Existing named-wall definitions, centre classification, side proofs and
  cyclic/unordered equivalences retain actual geometry. Reuse them only after
  constructing their precise simple/transversal hypotheses for the new path.

## Immediate implementation: polynomial avoidance for joint variables

Pinned Mathlib.Algebra.MvPolynomial.Funext supplies funext/funext_set. A nonzero
real multivariate polynomial has some nonzero evaluation by contraposition of
funext. Mathlib.Topology.Algebra.MvPolynomial supplies continuous_eval. These are
proved library theorems, not literature axioms.

For arbitrary scalar assignments x,y, define the line-restriction polynomial by
evaluating each variable into Polynomial.C(x_i)+Polynomial.X*Polynomial.C(y_i-x_i).
Prove that subsequent evaluation at t equals the actual multivariate evaluation
at x+t(y-x). Its value at1 is a chosen nonzero evaluation, so the univariate
polynomial is nonzero. Its roots are finite. Pull any nonempty open set back
along the continuous line and use finite-root avoidance near t=0 to prove density.
Then prove finite simultaneous nonvanishing on a nonempty open waypoint domain.
The general algebra/line/density/simultaneous-avoidance part now compiles in
work/checks/MultivariateAvoidance.prototype.lean (session78849 terminal0), with
five standard-only axiom traces and a result JSON beside it. It remains outside
the theorem library; read its independent prototype-review status in STATUS.md.
Do not reimplement it from scratch. After review, move its exact mathematical
body into a new module and add the concrete joint-waypoint pullback proofs.

Implement coordinate-selection pullbacks as rename maps for injective selections
of independent waypoint/scalar variables. Prove actual injectivity of each
selection, exact evaluation/hybrid identities, and resulting nonzero pullbacks.
Slopes/resultants live on the remaining-coordinate subtype; preserve that exact
domain in the selection maps. Scalar-step and vertex-coordinate-difference
constraints use distinct actual scalar variables; prove those differences nonzero.

## Geometric path construction

1. Build an actual scalar-coordinate homeomorphism for labelled tuples (the
   algebraic equivalence alone does not prove continuity). Use finite open boxes
   in the scalar space, with closures inside the regular locus and diameter less
   than the tolerance. Choose generic endpoint boxes. Handle the chosen norm
   and its relation to the source's uniform tolerance explicitly.
2. Prove a finite time subdivision subordinate to the pullback cover of the
   compact path image, refining to at least three subintervals. Retain strict
   ordered times, nonempty overlaps and the fixed original endpoints.
3. Select independent internal waypoints from consecutive overlaps. Define
   coordinate-by-coordinate hybrids in a fixed finite scalar order and prove
   each hybrid/leg stays in the same box. Parameterize all legs into the actual
   time interval; prove continuity, piecewise-affinity, endpoints, regularity
   and the strict uniform bound. The first/last polylines lie inside Generic.
4. On central legs impose joint nonvanishing of control values at both hybrids,
   every dependent slope and pairwise resultant, every moving scalar step,
   and both scalar differences for every distinct vertex pair at hybrids.
   Prove every required polynomial nonzero in the JOINT independent variables,
   then apply simultaneous avoidance in the open product of waypoint overlaps.
5. Prove each central leg has finitely many control roots, no endpoint roots,
   no common roots and genuine sign-changing simple roots; unused controls stay
   at their nonzero endpoint value. Prove vertex collisions impossible because
   the unmoved component separates the moving vertex from every other one.
   Fixed pairs stay distinct. Generic collars give collision-free endpoints.

## Classification and the active T calculation

All controls nonzero implies actual Generic: every point determinant is nonzero,
and any triple interior concurrence uses remote edges and forces one T to zero.
Use arbitrary-order coverage to reach the actual selected family member.

At a single area root, prove exactly one unordered collinear triple and no
concurrence. Retain collision freedom and regularity. Classify adjacency counts:
consecutive triple gives F (with the required strict betweenness); the n=3
collinear regular case is impossible. One adjacent pair gives interior V or
exterior E, and nonzero neighboring heights determine the two V branches.
No adjacent pair gives C. Prove exhaustiveness and uniqueness, not just cases
conditional on already having a named wall.

At a single active T root, all point determinants are nonzero, the unique actual
interior concurrence is the selected remote triple, and all pairs are transverse.
Prove the exact source identity
T_efg = -(t_ef-t_eg)*H_ef*H_eg
from the actual line rows, actual crossing point/parameters and determinant
algebra. Nonzero H factors retain their signs near the event. Thus the simple
T sign change implies the required crossing-parameter order sign change; repeat
cyclically for the other two. This identity is not yet implemented merely because
its printed derivation is supplied. Inactive T roots are omitted from events.

Finally assemble all event germs with actual finite isolated times and retained
labels, prove no cusp (regularity excludes its antiparallel centre), and obtain
independent full source/type/body review before accepting thm:relgp. Continue
with the remaining polynomial/carrier, transport/comparison, wall laws, soft
theorem and unconditional R development; this theorem is not the final goal.
