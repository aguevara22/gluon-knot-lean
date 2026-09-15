# Finish the actual finite family and nonassociation

The goal remains the complete original lem:transport-polynomials, then the full
thm:relgp and all corner state-sum wall laws, soft theorem and unconditional R.
Read STATUS.md for the latest completed audit. Do not count partial helpers as
original proofs, and do not edit previously reviewed SM files.

## Reuse the completed coefficient construction

CoordinateIsolation implements the exact isomorphism from the full scalar ring
to polynomials in one variable over the ring of all remaining variables. Its
slope and intercept reconstruct the original polynomial and evaluate correctly.
Degree at most one and actual variable membership imply a nonzero formal slope.

AffineResultant proves a nonzero remaining-variable resultant under explicit
irreducibility, affinity, dependence and nonassociation hypotheses. It derives
the result using primeness and degree-based nondivisibility. The concrete family
nonassociation hypothesis remains to be discharged; no original row is accepted.

RealAffineRoots and CoefficientSpecialization prove the source's specialized
root statements, including actual rootMultiplicity = 1. The no-common-root
result requires the evaluated resultant to be nonzero, without an extra
nonzero-slope condition. GeometricCoordinateSpecialization identifies evaluation
with the actual polygon obtained by varying exactly one scalar coordinate.

## Next executable proofs

1. Prove variables of a divisor are contained in those of its NONZERO dividend,
   using polynomial_not_dvd_of_degree_lt. Associated nonzero polynomials then
   have equal variable sets and equal vertex supports (image under Prod.fst).
   Prove that unequal evaluations at assignments differing only in one scalar
   force that scalar into the actual polynomial variable set.
2. Prove the area polynomial has exactly its three vertex labels as support.
   An explicit tuple with the middle vertex at (t,0), the last at (0,1) and the
   first at (0,0) evaluates to t. Prove cyclic polynomial identities and reuse
   this witness for every vertex. Prove absence of every outside coordinate.
3. Prove the concurrence polynomial has exactly its six endpoint labels as
   support. A useful representation is an injective six-slot endpoint map
   ![e,e+1,f,f+1,g,g+1]; injectivity follows from remoteness and next_ne_self.
   Function.Injective.extend_apply extends any six-slot tuple to the complete
   unrestricted labelled tuple. Prove each endpoint affects the determinant
   using explicit specializations; prove every outside coordinate is absent.
4. Different supports separate all such polynomials. Cardinalities three and
   six separate area from concurrence. A single chosen representative per
   unordered area triple removes the sign associates among areas.
5. Prove concurrence nonassociation for different triples, including equal
   endpoint supports, using the candidate below or the printed cycle argument.
6. Define the finite name type as the sum of cardinality-three vertex Finsets
   and cardinality-three pairwise-remote edge Finsets. Choose exactly one ordered
   triple per name, prove it has the stated unordered support, and prove every
   source control is represented up to its proved permutation sign. Do not omit
   names or retain all orderings as distinct names.
7. Assemble every source clause with the concrete family: nonzero,
   irreducibility, distinct-name nonassociation, coordinate affinity,
   remaining-variable decomposition/nonzero slope, nonzero resultant, and both
   specialized-root statements. Obtain full independent source/type/body review
   before accepting the original row, then run a current whole audit.

## CANDIDATE diagonal-collapse proof — not yet formalized

This may avoid classifying perfect matchings on the cycle. Suppose two triples
of disjoint edges have the same six endpoint labels but different unordered edge
pairs. Choose a pair (a,b) present only in the first triple. In the second triple,
a and b lie in two different edges. Give a and b the same point (0,0), their two
partners the respective points (1,0) and (0,1), and the remaining edge endpoints
the points (1,0) and (0,1). The first triple has a collapsed edge, so its line-row
determinant vanishes. The three lines of the second triple are y=0, x=0, x+y=1;
their determinant is nonzero (its sign depends on row and endpoint order).
Association would preserve vanishing under evaluation, a contradiction.

All of this remains UNPROVED until Lean checks the extension, cases, exact
determinants and evaluation/divisibility argument. Repeated point values are
allowed here: these are unrestricted polynomial specializations, not a claim
that the witness polygon is generic or regular. Arbitrary order and orientation
must be covered. Finally prove that in a cycle with n>=3 a directed edge is
uniquely determined by its unordered endpoint pair; the reverse-pair exception
would force 2=0 in ZMod n and contradict n>=3.

A finite six-slot proof can cover the possible positions of a and b in distinct
edge pairs. Use kernel-checked finite cases or explicit arithmetic proofs, never
native_decide. Keep the six-slot model connected to the actual full tuple by the
proved endpoint injection and extension. The printed n=6 witness remains a valid
fallback; a general proof need not single out that case if it includes it.

## After this lemma

Prove the entire thm:relgp, retaining labelled endpoints, uniform approximation,
regularity/collision freedom, finitely many isolated simple transversal named
walls and the exclusion of cusps. Preserve all later state-sum polynomial,
carrier, transport/comparison, wall-law, soft-theorem and unconditional R goals.
The independently verified zero-turn issue in the unrestricted shift lemma
remains local; it does not block this work or authorize altering the source.
