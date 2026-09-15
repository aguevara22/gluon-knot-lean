# Next full original proof: nonempty fibres and full generic density

UNPROVED PLAN. Source reference/SM/sm-1-polygons.tex, lem:fibres, lines 520–650.
The original row requires BOTH exact existence for all admissible integer
parameters and full Generic density in every nonempty open set of labelled
n-tuples for n>=3. A necessary-condition lemma, an individual seed, a merely
regular construction, or density for CV's weaker genericity is not the full row.

## Dependencies now available

The actual normalized rotation sum, integrality, regular-path constancy,
strict size bound, regular triangles, arbitrary edge-interior subdivision,
cyclic invariance and actual reversal are proved and independently reviewed
in lem:rot. Full uniform and one-opposite rotation is also accepted.
Admissible uses the exact integer inequalities/excluded pair; GenericFibre is
the actual rotation level set on the genuine cyclic quotient. Its DEFINE
review is finishing at checkpoint025/026. The unrestricted source lem:shift
has a separate confirmed counting omission; none of this proof needs that
false count. Use the already proved regular reversal directly.

## Full generic density

The printed construction uses actual area determinants for EVERY three
distinct vertex indices, together with the determinant of the three
homogeneous line-coefficient rows for each triple of pairwise remote edges.
Use ordered triples if convenient: prove that requiring every ordering is
equivalent to the source condition. Never replace all-triple G1 by the guarded
CV list. Empty remote-triple families contribute no restrictions.

For a directed edge from (x,y) to (x',y'), its line row is
(y-y', x'-x, x*y'-x'*y). Prove from actual coordinates that every point on the
closed edge satisfies its row equation. If three actual edge interiors meet,
G1 forces their edge indices pairwise remote (existing GenericTopology and
G1 geometry). The vector (point.x,point.y,1) is a nonzero kernel vector of the
three line rows, so their determinant vanishes. An explicit coordinate
elimination proof is also valid; no converse about projective concurrency is
required. Prove continuity of both determinant functions.

Each area determinant has the explicit nonzero witness assigning its three
vertices (0,0),(1,0),(0,1). Pairwise remote edges have six DISTINCT endpoint
indices; prove this before assigning their endpoint coordinates independently.
Use ordered endpoint pairs (0,0)->(1,0), (0,0)->(0,1), (0,1)->(1,1). Their line
rows are (0,1,0),(-1,0,0),(0,1,-1), with determinant -1. Repeated COORDINATES
across distinct indices are allowed in this witness, which serves only to
show a polynomial function is nonzero somewhere.

A potentially simpler proof of the required polynomial-avoidance fact uses
one real parameter and finite roots, avoiding a multivariate induction. This
is a PROPOSED alternative proof, not an assumption or implemented theorem:

1. For arbitrary tuples P,Q define the actual affine family
   tupleLine(P,Q,t)(i)=P(i)+t*(Q(i)-P(i)). Prove continuity, value P at 0 and Q
   at 1. For each determinant function construct the ordinary real polynomial
   in t obtained by substituting these actual affine coordinates. Prove its
   evaluation identity by ring-homomorphism/coordinate calculations.
2. For a function with a proved nonzero witness Q, this polynomial is nonzero
   for every starting P, because its value at 1 is nonzero. Its real root set
   is finite. The complement is dense in R, so it meets the nonempty open
   preimage of any neighbourhood of P under the actual affine family. This
   proves the nonvanishing set dense in the ENTIRE actual tuple space.
3. Each nonvanishing set is open by the proved coordinate continuity. The
   finite intersection of these open dense sets is dense. Every tuple in it
   satisfies all-triple G1 and, by the kernel-vector argument, full G2.
   Hence every nonempty open set contains an actual Generic tuple.

This proof still reconstructs the source's polynomial avoidance mathematically;
it does not postulate density, a perturbation oracle, or a generic witness
inside the desired neighbourhood. The supplied hpoly/witness premises of any
general helper must be PROVED for every actual determinant consumer.

Pinned source APIs inspected (types still need checking under chosen imports):
- Polynomial.finite_setOfPred_isRoot hp: finite roots for p!=0.
  finite_setOf_isRoot is its deprecated alias in this Mathlib pin.
- Dense.sdiff_finite removes a finite set from a dense set in a T1 space with
  nontrivial punctured neighbourhood filters (in particular R).
- dense_iff_inter_open / Dense.exists_mem_open give explicit witnesses.
- Set.Finite.dense_sInter proves the finite open-dense intersection statement
  without assuming a Baire-space theorem. Use finite_range for an index family.
- MvPolynomial.continuous_eval and MvPolynomial.hom_eval₂ are available if the
  multivariate substitution representation proves cleaner. They are optional.

## Existence in every admissible fibre

Necessary conditions follow from the actual strict rotation bound and triangle
lemma, including exclusion of (3,0). Keep the source's integer parameter domain:
if vertex counts are represented by naturals, prove the equivalence with a
nonnegative integer count and n>=3 rather than silently omitting integer cases.

For positive integer r, construct m=2*r+1 complex vertices q^j, with
q=exp(i*2*pi*r/m). Prove q^m=1 and q!=1, actual edges q^j*(q-1) including the
wrap edge, and actual successive edge ratios q. Since the angle is strictly
between 0 and pi, prove the principal turn is that angle using the exact
cosine/sign uniqueness or argument multiplication on the regular slit plane.
The total rotation is r. Distinct vertices may be proved from gcd(r,m)=1 but
are not a hidden prerequisite for the regular seed. Negative seeds are its
actual reversal. For zero use the printed bowtie; prove its regularity and
actual principal-angle cancellation or a proved symmetry giving rotation 0.

Iterate the already proved actual insertVertex construction to reach every
n>=m, retaining regularity and rotation. Prove the regular locus open on its
full domain (positive collinear turns allowed); rotor slit-plane openness is
one available route. Obtain a convex neighbourhood inside Regular, so the
actual straight path from the refined seed to each point preserves rotation.
Use the FULL Generic density theorem to choose a Generic point there.

Assemble necessity, sufficiency and the complete density clause. Obtain
independent full source/type/body review before accepting lem:fibres. None of
the intermediate work increments the fixed original proof count by itself.
