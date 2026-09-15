# Next required chain after the named-wall definition

Finish and audit original def:walls before executing this plan. Its source
predicates and conventions are now implemented; do not redo accepted wall-sides,
cusp-sides, children, or the new full definition after acceptance.

The next original proof is lem:transport-polynomials, in
reference/SM/sm-1-polygons.tex:1292–1383. It supplies the finite algebraic
controls for thm:relgp, which is required by the transport/comparison route to
the full cusp wall law. This is a required part of the existing focused goal,
not an alternative target. All main state-sum laws, the soft theorem and R
remain required and incomplete.

## Exact scope

Use actual scalar coordinates of the labelled tuple, with indices
ZMod n × Fin 2 and coefficients ℝ. An explicit equivalence with the source's
2n scalar variables is acceptable; prove evaluation back to the actual Plane
coordinates. Do not replace polynomials with arbitrary analytic functions.

For each unordered three-vertex support, choose one ordered representative
of the actual area determinant Δ. For each unordered triple of pairwise remote
edges, choose one representative of the determinant T of the actual line rows
(-d_y, d_x, det(μ,d)). Remote edges have six distinct endpoint occurrences.
Retain one representative per support so sign associates are not counted twice.

Required conclusions, all still open:

1. Each Δ and T is nonzero and irreducible over ℝ, in the full coordinate ring.
2. Distinct named members are nonassociate. Distinguish three-vertex/six-endpoint
supports and prove actual dependence on every included endpoint. Handle the
two alternating matchings on the full n=6 cycle using the printed witness.
3. Every member has degree at most one in each individual scalar coordinate.
If it actually depends on a coordinate, its slope in that coordinate is nonzero.
4. For distinct members a*x+b and c*x+d both depending on the chosen coordinate,
prove ad-bc nonzero in the remaining-variable ring. This uses irreducibility,
coprimality and unique factorization; it must not be assumed as a generic oracle.
5. Prove specialized root simplicity and absence of a common root under the
printed nonvanishing conditions. A coefficient identity alone does not replace
the irreducibility or nonassociation clauses.

## Implementation steps

First build the concrete multivariate coordinate/line-row/determinant model
with evaluation identities. Reuse existing PolynomialAvoidance, determinant
geometry and cyclic index lemmas as needed; the ordinary polynomials along
tuple lines do not by themselves prove multivariate irreducibility.

Then implement the irreducibility of the basic two-by-two determinant and its
transport by invertible linear coordinate changes and unused-variable extensions.
The printed rank-four quadratic argument is available; another fully proved
algebraic argument is acceptable. The follow-up pinned-Mathlib search found
Mathlib/RingTheory/MvPolynomial/IrreducibleQuadratic.lean. Its
MvPolynomial.irreducible_sumSMulXSMulY proves irreducibility of a primitive
bilinear sum with at least two nonzero terms; coefficients 1 and -1 are a
candidate for the basic determinant, after an explicit variable permutation.
Its irreducible_mul_X_add and irreducible_of_disjoint_support are also relevant.
Read their actual hypotheses and prove the concrete substitutions; the search
result is not itself an irreducibility proof of Δ or T.

For isolating one coordinate, the pinned
Mathlib/Algebra/MvPolynomial/Equiv.lean supplies renameEquiv and
optionEquivLeft. The latter identifies an Option-indexed coordinate ring with
ordinary polynomials in the distinguished variable over the remaining-variable
ring, with explicit X/constant/evaluation and degree identities. This gives a
concrete route to the printed a*x+b and resultant clauses.

For T, use independent tail/direction coordinates and its printed expansion
as a linear polynomial in the last direction pair. Prove coprimality of its
two coefficients using the auxiliary irreducible remote-direction determinant
and the explicit parallel-line specialization. Preserve every specialization
and coefficient comparison used to exclude a common nonunit factor.

Obtain independent statement/body review and a current whole audit before
accepting the original proof row. Partial helpers never raise 13/132 on their
own. Keep all currently reviewed SM files unchanged and implement in new work
modules. No literature interface is needed here, and no author answer is needed.

After this full lemma, execute the complete relative-general-position theorem
(same labelled endpoints, uniform approximation, regular/collision-free path,
finite isolated simple F/V/T/E/C germs, occurrence labels retained, no cusp).
Transport connectivity, the amplitude/polynomial chains, all direct C laws,
the soft theorem and unconditional R remain part of the same goal.
