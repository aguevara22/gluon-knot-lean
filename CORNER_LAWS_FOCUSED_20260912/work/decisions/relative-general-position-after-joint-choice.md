# Relative general position after the actual joint choice

Read STATUS.md for build/review/audit status. Preserve all reviewed SM modules;
use new modules. The full original thm:relgp and the main wall-law/soft/unconditional
R goal remain incomplete. This work is supporting mathematics, not an extra source
claim or a replacement target.

## Concrete joint variables and conditions

SM.WaypointOpenDomain imports the exact finite simultaneous avoidance port and
the accepted concrete polynomial controls. Its theorem
`SM.exists_joint_waypoint_conditions_in_domains` takes:

- n≥3 and the redundant NeZero n instance;
- a finite type κ of internal waypoint labels and a finite type ι of central legs;
- each leg's distinct left/right waypoint labels, moving scalar coordinate, and
  already-switched set excluding that moving scalar;
- an actual nonempty open set O k of scalar assignments for each internal waypoint.

It produces ONE assignment W of all κ×(ZMod n×Fin 2) scalar variables such that
every waypoint lies in its prescribed set and all conditions hold on every leg.
No nonzero-polynomial assumption or result about projections of open sets is
supplied: injective renaming proves all pullbacks nonzero. Keeping the original
scalar as the second component proves injectivity even when different coordinates
choose different waypoints. Fixed-coordinate coefficients use exactly the subtype
excluding the moving scalar. Distinct actual left/right tags prove the step
polynomial nonzero; distinct vertices prove each coordinate difference nonzero.

`SM.JointLegConditions` is transparent and has exactly the required five fields:
endpoint_controls, dependent_slopes, pair_resultants, scalar_step,
vertex_differences. Resultant conditions retain both actual dependence premises.
`SM.jointLegConditions_iff` proves equivalence with all evaluations of the finite
condition family. The source's fixed original endpoints must stay outside this
independently variable κ space; their collars still need construction.

SM.ScalarCoordinateTopology supplies the scalar coordinate homeomorphism for the
actual labelled tuple/product topology. It does not identify the max product
metric with the Euclidean metric. SM.CentralLegCollision proves the explicit leg
assignment equals the affine scalar line, hence is continuous; the other Fin 2
component remains unchanged at every vertex and separates every distinct pair,
so each actual tuple on the entire leg has injective vertex positions.

## Next algebraic work

For a leg, a named control p, fixed assignment η, and t∈ℝ, isolate the actual
moving scalar x(t)=x0+t*d, where d is the proved nonzero scalar step. Use
eval_coordinate_affine and the actual assignment definition to prove:

1. The univariate parameter restriction is the actual real affine polynomial
   with slope evalη(coordinateSlope p)*d and constant eval(endpoint false)p.
   Prove the evaluation identity explicitly, including the endpoint constant.
2. If the moving scalar is absent from p.vars, its coordinate degree is zero,
   so coordinateSlope p=0 and the restriction stays at the nonzero endpoint value.
3. If the moving scalar occurs, the chosen slope and d are nonzero. Therefore
   the parameter restriction has one simple root and changes sign there. Restrict
   to the leg interval only after proving the all-real algebraic statement.
4. Two dependent controls cannot share a parameter root, by actual coefficient
   specialization and the chosen nonzero resultant. If either is independent,
   its nonzero constant already excludes a common root. Neither endpoint is a root.
5. Prove finiteness of all roots across the finite control-name and central-leg
   families; preserve which named factor vanishes. Inactive concurrence roots
   are not automatically nongeneric events.

## Still required for the full original statement

Construct open scalar boxes with closures in the actual Regular locus and
Euclidean diameter bounds. Prove the finite time subdivision subordinate to the
path cover and nonempty consecutive box overlaps, with Generic endpoint collars.
Apply the joint-choice theorem to these actual overlap sets and actual central
coordinate legs. Prove all hybrids and legs stay in the correct box, assemble
the continuous piecewise-affine path with fixed labelled endpoints and the exact
uniform tolerance, and retain regularity/collision freedom.

Then classify isolated events into actual F, both V branches, T, E, C, excluding
cusps by regularity. Prove the actual T/crossing-parameter determinant identity
and its three order sign changes. Handle inactive T roots correctly. All of the
remaining source conditions and the final aggregate require independent review
before accepting the one original thm:relgp row. No author question is needed.
