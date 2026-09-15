# Next original proof — uniform and one-dissent rotation

COMPLETED AND INDEPENDENTLY ACCEPTED at checkpoint 024. Source: reference/SM/sm-1-polygons.tex, lem:uniformrot,
lines 428–453. The plan below is retained as a design record; all four source cases are now
implemented in SM.uniform_rotation and reviewed in reviews/lem-uniformrot.json.
The source has BOTH the all-left/all-right clauses and the exactly-one-opposite
clauses. Completing only the uniform case does not complete this source row.

The concrete rotation number, complete regular domain, cyclic invariance,
reversal, integrality, continuity, insertion, triangles and strict bound are
now implemented in the preceding branch. Keep their independently reviewed
source files unchanged. Implement this next branch in new modules.

## A common positive-case theorem

One useful stronger intermediate statement is: on an actual regular polygon,
if every principal turn except possibly index 0 is strictly positive, the
actual rotation number is positive. Its proof must use closure of the actual
edge vectors. Integrality then upgrades positive rotation to rotation at least
one. This intermediate, once PROVED, covers both required positive cases after
a cyclic shift; it does not replace the source's stated hypotheses or target.

At an arbitrary source right-turn index a, shift by a so that this corner is
index 0. This differs intentionally from insertion's shift by a+1. Prove every
other shifted index reads a different original index, and translate turn sign
to principal-angle sign using principalAngle_sign and turn_det. The all-left
case supplies the same off-zero positivity with any cut. Use the already
proved rotationNumber_shift to return to the original tuple.

## Actual cumulative edge directions

For a natural k<n, define B(k) as the real sum of principal turns at indices
1 through k, using natural casts into ZMod n. Set L=B(n-1). Prove from the
off-zero positivity that 0<=B(k)<=L. Prove the exact complete sum identity
sum(theta)=theta(0)+L by a bijection between Fin n and ZMod n and a finite-sum
split; do not assume a turn inventory. If rotation<=0, this identity gives
L<=-theta(0)<pi, using the source strict principal-angle bound at index 0.

Let A(k) be the actual argument class of planeComplex(edge P k) in Real.Angle.
The proved principalTurn_coe_angle identifies each consecutive difference.
Telescoping over natural k yields A(k)=A(0)+(B(k):Real.Angle). Only this quotient
identity is required. Do not assert an unwrapped equality of principal edge
arguments in R, because an edge direction may cross the argument cut.

Finite prefix sum and natural-cast bounds must include k=0 and k=n-1. Every
actual edge is represented by k=i.val, with k<n and natCast_zmod_val. Check
the pinned precise APIs for the finite range telescoping and Fin/range sums;
if necessary prove the elementary finite-sum transport from a concrete
bijection. The earlier InsertionSum illustrates a verified image-partition
argument, but is not directly this prefix-sum identity.

## Construct a strictly positive linear functional

Take c=arg(planeComplex(edge P 0))+L/2 and the actual real vector
u=(cos(c),sin(c)). Prove the coordinate identity
planeDot u (edge P i) = euclideanLength(edge P i) * cos(B(i.val)-L/2).
Use the just-proved Real.Angle identity to compare cosines; cosine is a
well-defined function on that exact 2*pi quotient. Do not eliminate the
integer-period discrepancy by assuming zero winding at individual edges.

The coordinate reconstruction facts are already in the pinned Arg file:
Complex.norm_mul_cos_arg and Complex.norm_mul_sin_arg. Real.cos_sub gives the
dot-product expression. Real.Angle.cos_coe transports the equality of angle
classes back to the real cosine. Verify the precise elaborated types when
implementing; preserve the actual Euclidean length, not Plane's product norm.

Because 0<=B(k)<=L<pi, the centered angle is strictly between -pi/2 and pi/2.
Real.cos_pos_of_mem_Ioo then gives a positive cosine. All actual edges are
nonzero by Regular, so their Euclidean lengths are strictly positive. Therefore
every actual dot product with u is positive. Sum these inequalities over the
nonempty cyclic finite index set. Linearity in the second argument and the
already proved sum_edges P=0 make this same sum zero, a contradiction. This
constructs the source dual-cone witness explicitly; no separation theorem,
positive-functional oracle, or external literature assumption is needed.

Conclude rotation>0. Extract its proved integer witness and use integer order
to obtain rotation>=1. Mirror both required cases by the actual reversal map:
Regular is preserved, turn signs reverse under i->2-i, and rotation negates.
Track the exceptional index exactly rather than supplying an unspecified
permutation or assuming the desired right/left pattern after reversal.

## Acceptance boundary

Assemble all four source implications, with actual Regular P and the source
all-turns-nonzero condition. A precise unique-exception formulation can use
an actual exceptional index together with the opposite sign there and the
uniform sign at every other index. Prove equivalence if a different predicate
is chosen. No helper or partial uniform clause increases the original count.

Register the complete source theorem, run the whole-project audit, obtain
independent source/type/body review, verify semantic and file hashes, and only
then accept lem:uniformrot. Continue toward the carrier bound and main corner
wall/soft targets; this remains only one dependency in the full objective.

## Pinned API checks completed after the rotation proof

The following types were inspected with the pinned Lean environment:

- Finset.sum_range_sub f k telescopes sum over j<k of f(j+1)-f(j) to f(k)-f(0).
- Finset.sum_range_sub' uses the opposite sign convention.
- Fin.sum_univ_eq_sum_range f n identifies the Fin n sum of f(i.val) with
  the range n sum of f(i). There is no primed variant under the checked imports.
- Finset.sum_range_succ' splits range(n+1) as sum over j<n of f(j+1), plus f(0).
- Real.Angle.cos_coe identifies angle-class cosine with real cosine.
  Real.Angle.cos_sub was not found; use equality of angle classes followed by
  congrArg Real.Angle.cos and cos_coe, then real trigonometric identities.
- Complex.norm_mul_cos_arg and norm_mul_sin_arg reconstruct real/imaginary
  coordinates from actual norm and argument.
- Real.cos_pos_of_mem_Ioo takes strict bounds -pi/2 < x < pi/2.

Full lem:rot is independently accepted in reviews/lem-rot.json. None of these
API checks alone constitutes a proof; the completed implementation and
independent full review are now bound by checkpoint-024-output.json.
