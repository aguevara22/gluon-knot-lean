# Completed branch — principal turns and rotation number

UPDATE 2026-09-10: full def:regular and full lem:rot are independently accepted
in reviews/def-regular.json and reviews/lem-rot.json. All rotation clauses,
including actual vertex insertion on every edge, are proved. The next original
source row is lem:uniformrot; see uniform-rotation-next.md. The design below is
retained to explain the completed domain and rotation scope. These results feed
the later carrier rotation bounds and state sum.

## Principal turns and the regular domain

Define the regular predicate on actual edge vectors: every edge is nonzero and
no edge is a negative real multiple of its predecessor. Do not substitute G1
for regularity: positive collinear successive edges and zero principal turns
are explicitly allowed. Prove G1/generic implies regular as a consequence.

Use the coordinate map Plane=R×R -> C, (x,y) -> x+iy. Define Euclidean length
through its complex norm and prove the sqrt(x*x+y*y) formula. The existing
product-space norm on Plane is not the source Euclidean length; do not use it
silently in the cosine denominator. The dot product is x1*y1+x2*y2.

A concrete candidate principal turn is Complex.arg(conj u * v), with u,v the
complex images of the incoming/outgoing edge vectors. Its real part is the
actual dot product, imaginary part the actual determinant, and norm the product
of the two Euclidean lengths. Nonzero and non-antiparallel hypotheses put this
product in the slit plane; the source interval is strictly (-pi,pi), not the
library's generic (-pi,pi] argument range.

Prove the exact cosine and sign clauses, uniqueness on that open interval,
equivalence of regularity and existence at every corner, and turn zero iff a
positive multiple. Bind the full source row and cyclic representative transport
before independent review; defining an arg expression alone is insufficient.

Pinned APIs inspected in Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:
Complex.cos_arg requires a nonzero complex input; sin_arg is unrestricted;
neg_pi_lt_arg and arg_le_pi give the basic range; arg_eq_pi_iff is negative real
part plus zero imaginary part; arg_lt_pi_iff excludes that case;
arg_eq_zero_iff is nonnegative real part plus zero imaginary part;
arg_neg_iff compares signs of argument and imaginary part;
continuousAt_arg holds on Complex.slitPlane. Mathlib/Analysis/Complex/Arg.lean
imports that file and additionally relates arguments to SameRay. Check each
precise type before using it, especially the positive/zero edge cases.

Further pinned APIs: Real.injOn_cos is injectivity on Icc 0 pi, useful after
using the prescribed sign to compare absolute angles. Complex.arg_conj_coe_angle
negates the angle class for every complex input; Complex.arg_mul_coe_angle
requires both factors nonzero. Real.Angle.coe_eq_zero_iff identifies a real
angle class equal to zero with an integer multiple of 2*pi. These can justify
the finite telescoping proof without treating integrality as an input.

## Full rotation lemma

Prove all five source clauses, not only integrality:

1. The actual finite sum of principal turns divided by 2*pi is an integer.
   The source proof multiplies normalized complex edge directions around the
   cycle. An alternative is to prove the same telescoping identity in
   Real.Angle and then use its proved 2*pi quotient relation. Any integer-valued
   representation must be proved equal to the source real sum, never assumed.
2. Prove continuity of actual turns on the regular locus, then constancy along
   genuine continuous regular paths from the integer-valued result.
3. Construct actual edge-interior vertex insertion for arbitrary edge and
   parameter 0<t<1, with the resulting n+1 tuple and correct traversal. Prove
   regularity and the exact finite-sum identity (one added zero turn), including
   the label cut and cyclic equivariance. Reversal must use the already proved
   concrete map i -> P(2-i); prove the principal-turn negation and sum transport.
4. For regular triangles, prove the common determinant nonzero: three collinear
   nonzero closing edges force an antiparallel consecutive pair. Then use the
   common sign, strict principal-angle bounds and integrality to derive the
   signed unit rotation and all three turn equalities.
5. Sum strict absolute angle bounds to obtain the strict 2*abs(rot)<n bound.

Do not count helpers or partial rotation clauses as an accepted original proof.
Review complete statements, inherited domains and alternative representations
independently. No new literature input or axiom is needed for this branch.

## Scope still outstanding

The main targets remain all eight wall/soft roots, including unconditional R
discharge. The source's weak-locus extension of visible signatures belongs to
lem:silentlocus and later silent-wall work, not the generic def:visible row.
Its geometry must be formalized on WeakGeneric without silently assuming G1;
add that dependency if a retained consumer requires it despite absent DAG edges.
