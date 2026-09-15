# Finish polynomial controls after irreducibility and coordinate degree bounds

The target remains the COMPLETE original lem:transport-polynomials,
sm-1-polygons.tex:1292–1383, then the full thm:relgp. Do not accept a subset of
its clauses as the original. No main state-sum law or soft theorem is complete.
Read STATUS.md for the current whole receipt and independent partial reviews.

## Implemented mathematics to reuse

SM.CoordinatePolynomials and SM.DirectionPolynomials give the actual Δ/H,
geometric evaluation, full scalar/tuple equivalence, and explicit invertible
coordinate changes. Both polynomials are irreducible/nonzero in the full ring.

The seven new modules after audit048 are:
PolynomialLinearCore, LinearConcurrenceCore, LinePolynomials,
FirstTwoLinePolynomials, ConcurrencePolynomialIrreducible,
CoordinateAffinity, ConcurrenceAffinity.

The actual concurrencePolynomial is the determinant of the source's line rows,
with evaluation equal to the existing concurrenceDet. T irreducibility and
nonzeroness are proved under exactly n≥3 and three pairwise remoteness conditions.
The proof uses primitive-linear irreducibility twice: C and A are relatively
prime because C is irreducible and the explicit FORMAL tail/direction witness
has C=0,A=-1; the next divisor is excluded by degree in the last tail x-variable.
An explicit shear then identifies this free polynomial with the actual T.
The witness's raw head slots represent directions BEFORE the shear, not geometric
heads of parallel edges in that raw tuple. Preserve this distinction in reports.

CoordinateAffinity proves areaPolynomial.degreeOf z≤1 for every actual scalar
coordinate, with no distinctness needed for this bound. ConcurrenceAffinity
proves concurrencePolynomial.degreeOf z≤1 for three remote edges. It bounds
each line row and proves a coordinate can affect at most one selected row.
These are exact degree bounds, not yet the complete remaining-variable coefficient
decomposition and nonzero-slope assertion of the source.

Keep all currently reviewed/audited SM files unchanged; implement new modules.

## Immediate next implementation: isolate a scalar and produce its coefficients

For σ=ZMod n×Fin2 and scalar i, use the actual algebra equivalence
(renameEquiv ℝ (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft ℝ _)
from MvPolynomial σ ℝ to Polynomial (MvPolynomial {j // j≠i} ℝ).
Prove its generator maps and evaluate it back to the actual assignments.

Pinned Algebra/MvPolynomial/Equiv.lean:824 degreeOf_eq_natDegree identifies the
degreeOf i with natDegree of this exact representation. Apply the proved degree
bounds and Algebra/Polynomial/Degree/SmallDegree.lean:41
eq_X_add_C_of_natDegree_le_one to obtain a=coeff1,b=coeff0 in the remaining-variable
ring. Prove the inverse-map expression F=a*x_i+b and all evaluation identities.
Actual dependence is i∈F.vars (equivalently degreeOf i≠0); prove it forces a≠0.
Do not use evaluated nonzero slope as a substitute for formal nonzero slope.

## CANDIDATE simplification for the nonzero resultant — not yet proved

Instead of reconstructing both coefficient gcd arguments, use primeness of the
irreducible F in the full polynomial UFD. If ad-bc=0, the explicit linear formulas
give c*F=a*G. Thus F divides a*G. It cannot divide the nonzero a, because F has
degree one in the chosen scalar and a has degree zero; the already proved
polynomial_not_dvd_of_degree_lt supplies this exclusion. Primeness then gives
F∣G. Since both are irreducible, they are associated, contrary to the required
nonassociation. Prove every premise and the identity; this is a candidate until
kernel checked. It does not replace the separate nonassociation proof.

Inspected pinned tools: RingTheory/Polynomial/UniqueFactorization.lean provides
MvPolynomial.uniqueFactorizationMonoid; Algebra/GroupWithZero/Associated.lean:268
provides Irreducible.associated_of_dvd. Degree arguments must retain the nonzero
dividend premise. The specialized linear-root and no-common-root statements still
require explicit proofs over real specializations and the source's nonzero tests.

## Required family and nonassociation work

Construct the finite family with one ordered representative per unordered
distinct vertex triple and per unordered triple of pairwise remote edges.
Prove the representative covers exactly the source controls; do not keep all
sign associates or delete difficult members.

Prove actual variable support/dependence. Each Δ uses its three vertex labels;
each T uses its six endpoint labels. Independence of all other vertices is
already accessible from polynomial variable bounds. Every included endpoint
must actually affect the polynomial; no qualitative geometric claim may be
used as an oracle. Explicit pairs of specializations differing in one scalar
coordinate can establish dependence via eval₂Hom_congr' (Variables.lean:271),
or prove nonzero coefficients directly. Any specialization construction is still
unproved until its endpoint inequalities and evaluations are kernel checked.

Associated polynomials must have identical actual vertex supports. This separates
Δ/T and all different supports. For a fixed six-vertex support, prove the cycle
perfect-matching argument, including wraparound: a proper induced subgraph is a
union of paths, each with at most one perfect matching; only the full n=6 cycle
can admit the two alternating matchings. Verify the printed tuple
((1,0),(2,0),(0,1),(0,2),(1,1),(2,2)) gives T135=0,T246=2 with the chosen row order.
Explain any sign from another representative with a proved permutation identity.

A CANDIDATE alternative to formalizing path components is to prove matching
uniqueness by propagation around the actual cycle. At every supported vertex,
exactly one of the two incident cycle edges belongs to the matching. If two
matchings have the same endpoint support, agreement on one edge therefore
propagates to the next. A missing vertex initializes agreement (both incident
edges absent), forcing equality around the whole finite cycle. Hence distinct
matchings with the same six-vertex support force that support to be the full
cycle and n=6. The resulting finite six-cycle classification may be proved by
kernel-checked decide if its exact domain and predicates are computable; never
use native_decide. This propagation argument and the classification are still
UNPROVED and require the actual coverage/disjointness, modular induction and
cardinality obligations. They must not be introduced as assumptions.

## Acceptance and continuation

Only after all irreducibility/nonzero, family/nonassociation, degree/decomposition,
slope/resultant and specialized-root clauses are present, assemble a source-facing
aggregate, obtain independent full statement/body review, map the original row
and run a current whole audit. Helpers do not change 13/132 original proofs.

Then prove all clauses of thm:relgp: same labelled endpoints, uniform approximation,
regular/collision-free path, finite isolated simple F/V/T/E/C occurrences with
labels retained and no cusp. Preserve the full remaining state-sum polynomial,
carrier, transport/comparison, wall-law, soft-theorem and unconditional R goals.
