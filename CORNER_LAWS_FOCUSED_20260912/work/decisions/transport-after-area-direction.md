# Continue the original polynomial-controls lemma after Δ and H

The complete source remains sm-1-polygons.tex:1292–1383. No original claim is
accepted by these partial modules. Do not redo reviewed wall geometry.

## Implemented portion

- SM.DeterminantPolynomial proves irreducibility of X a * X b - X c * X d
  in an arbitrary ambient polynomial ring over ℝ. It uses an inspected primitive
  linear polynomial theorem, with the required coprimality proved from prime
  variables. Extra ambient variables remain in the ring throughout.
- SM.PolynomialShear constructs subtraction and addition algebra homomorphisms,
  proves both compositions are the identity, and packages their algebra equivalence.
- SM.CoordinatePolynomials uses exactly ZMod n × Fin 2 scalar coordinates.
  Scalar assignments and actual labelled tuples are mutually inverse. Evaluation
  of areaPolynomial is the actual determinant of the two vertex differences.
  An explicit base-vertex translation proves Δ irreducibility and nonzeroness.
- SM.DirectionPolynomials gives actual edge-direction coordinates and their
  evaluation identities. SeparatedEdgeHeads is an explicit condition on edge
  labels; remote pairs satisfy it. The tail/direction change proves H irreducible
  in the full ambient ring. Its Nontrivial(ZMod n) condition follows from source
  n≥3; retain that discharge in the eventual full source theorem.

Check STATUS.md for current audit and independent partial review. These four
modules and earlier accepted modules must remain unchanged after review; add
new modules for later arguments. The old Bool⊕Bool prototype is separately
reviewed and is superseded for actual Δ/H transport by this implementation.

## Immediate next work: actual T polynomial and evaluation

Reuse SM.LineConcurrence's edgeLineA/B/C, edgeLineRow, concurrenceMatrix and
concurrenceDet. Define their multivariate counterparts and prove evaluation
equals these actual functions. Prove the polynomial 3×3 determinant expansion.
Do not infer this identification from zero-set agreement.

For three pairwise remote edges prove SeparatedEdgeHeads {e,f,g}. Extend the
current shear with lemmas that selected tails are fixed. The selected heads
are already mapped to their actual directions. Prove the transformed polynomial
is the exact T, using the printed line rows and expansion, including signs.

## CANDIDATE proof route for T — not yet formalized or certified

In independent tail/head coordinates treat the head variables as the direction
coordinates before applying the shear. Let (A,B,C) be the cross product of the
first two line rows. Then C is their direction determinant, and
T = d_g,y * (μ_g,x*C-A) + d_g,x * (B-μ_g,y*C).

An alternative to the source's common-divisor argument may use the primitive
linear theorem twice. First prove C and A coprime: C is irreducible; the explicit
specialization with tails (0,0),(0,1) and both directions (1,0) gives C=0,A=-1,
so C cannot divide A. Consequently μ_g,x*C-A is irreducible as a linear polynomial
in μ_g,x. Prove its degree in μ_g,x is one. The other coefficient B-μ_g,y*C
is nonzero (degree one in μ_g,y); multiplied by d_g,x it stays nonzero and
independent of μ_g,x. Degree additivity then excludes divisibility by the first
coefficient. This proves coprimality for a second application of
irreducible_mul_X_add in d_g,y, after explicitly checking that neither coefficient
depends on d_g,y. All variable-separation and coefficient claims need proofs.

Inspected pinned Mathlib tools for these obligations:
- RingTheory/MvPolynomial/IrreducibleQuadratic.lean: irreducible_mul_X_add.
- Algebra/MvPolynomial/NoZeroDivisors.lean: degreeOf_mul_eq, for two nonzero factors.
- Algebra/MvPolynomial/Degrees.lean: degreeOf_mul_X_eq_degreeOf_add_one_iff,
  degreeOf_add_eq_of_degreeOf_lt, ne_zero_of_degreeOf_ne_zero.
- Algebra/MvPolynomial/Variables.lean: mem_vars_iff_degreeOf_ne_zero, vars_mul,
  vars_C_mul. Negative terms can be written C(-1)*p for exact variable control.

If this candidate route fails, investigate the failed premise or return to the
printed coefficient-gcd argument. It never licenses a new axiom or a stronger
source hypothesis.

## Remaining original clauses

After T, prove the support-dependence and nonassociation statements, including
the possible two n=6 alternating matchings and the printed 0/2 witness. Prove
affinity in each scalar variable, nonzero slopes on actual dependence,
nonzero ad-bc for distinct named controls, and both specialized-root assertions.
Choose one representative per unordered support, retaining every source member.
Keep the original source row pending until all clauses pass independent review.

Then implement the full thm:relgp, not only a polynomial avoidance helper.
All state-sum wall laws, the soft theorem and unconditional R remain required.
