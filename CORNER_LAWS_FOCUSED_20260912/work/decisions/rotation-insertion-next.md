# Completed rotation clause — actual vertex insertion

COMPLETED 2026-09-10. Full original lem:rot is independently accepted in
reviews/lem-rot.json, including actual edge-interior vertex insertion.
AngleScaling, InsertionIndices, InsertedTuple, InsertionSum, AppendRotation,
VertexInsertion and RotationTheorem implement this branch. Old indices retain
their natural representatives; a proved complete finite-set image partition
gives the sum identity. All 24 supporting-file hashes are bound to the full
independent review and candidate checkpoint 021. The partial checkpoint 020
report is historical: its missing insertion clause is now proved.

Next work is lem:uniformrot; see uniform-rotation-next.md. The design record
below explains the completed construction and the scope that was checked.

## Construction and index convention

Use the source's explicitly permitted labelled/equivariant formulation. For an
arbitrary old edge i, first shift the tuple by i+1. Its last old edge, indexed
-1, is exactly the chosen original edge i, and its first old vertex is P(i+1).
Append the new vertex edgePoint P i t for 0<t<1 after that last old vertex.
Thus the new cyclic traversal lists every original vertex in its original
cyclic order and visits the actual inserted point between P i and P(i+1).
This cyclic cut is allowed; it must be proved to represent actual insertion,
not used to assume invariance under an arbitrary replacement tuple.

A possible implementation builds the appended tuple on Fin(n+1) with
Fin.lastCases: on castSucc j use the shifted old tuple at the ZMod n image of
j; on Fin.last n use the actual edge-interior point. Transport through the
proved ring equivalence ZMod.finEquiv(n+1). Expose vertex formulas for every
old index and the inserted index before proving anything about angles.
The inherited source bound n>=3 avoids coincident first/last old vertices.

Prove all actual edge formulas. Unsplit edges are unchanged. The last old edge
becomes t times its old vector, and the inserted vertex's outgoing edge is
(1-t) times that same vector. Treat wraparound explicitly. Prove the inserted
point lies in the source edgeInterior from the actual parameter inequalities.
Do not replace insertion by a supplied list of angles or an abstract multiset
identity: the angles must be those independently computed on this new tuple.

## Angle and sum identities

First prove principalAngle unchanged by independently multiplying incoming and
outgoing vectors by positive real scalars. The actual cornerRotor then changes
by the positive product scalar. Pinned API already inspected:
Complex.arg_real_mul (x : C) (hr : 0<r) proves arg(r*x)=arg x;
Complex.arg_mul_real proves the right-multiplier counterpart. Use the existing
planeComplex_smul and the coordinate rotor formula to justify that scalar law.
Prove corresponding RegularPair preservation, either from exact scalar
geometry or from the proved principal-angle specification equivalence.

For every old vertex, compare both actual adjacent edge vectors and prove its
new principal turn equals the old one. At the new vertex both vectors are
positive multiples of the same nonzero old edge, so the proved positive-scalar
criterion gives a zero turn. Establish Regular of the new tuple on every index.

Use Equiv.sum_comp for the finite ZMod/Fin transports and
Fin.sum_univ_castSucc for the new n+1 sum: all old turns plus the last zero.
Pinned Fin.sum_univ_castSucc and Fin.sum_univ_succ are present in the current
Mathlib import chain. Check their precise elaborated types before use.
Conclude the actual real rotationNumber is unchanged, then remove the initial
cyclic cut with the already proved rotationNumber_shift.

## Completion and review

Assemble one theorem for every source clause at arbitrary n>=3 and regular P,
including insertion at every actual edge and every parameter in (0,1), actual
reversal, genuine continuous regular paths, regular triangles and the strict
bound. The source real rotationNumber is sum/(2*pi); integrality is its proved
equality to an integer, never a supplied winding-number input.

Register only the complete aggregate as lem:rot. Request independent review of
its entire statement and all supporting definitions/proofs, including the
actual n+1 insertion geometry. Run the whole-project audit, verify the semantic
hash and reviewed file hashes, and only then accept the original source row.
Partial helpers do not increase the original 132-proof denominator.

## Pinned implementation lessons

- A real sum cast to Real.Angle needs an explicit inner real type annotation;
  otherwise elaboration may instead sum already coerced summands. The current
  RotationNumber theorem and map_sum proof use the explicit real annotation.
- Equiv.coe_addRight is needed when simplifying sum_comp; subtraction may need
  sub_eq_add_neg. Equiv.subLeft is the actual i -> a-i permutation.
- For ContinuousAt.comp on a curried rotor, specify f, x and g explicitly to
  prevent the first argument's elaboration selecting the last curried input.
- Concrete ZMod 3 arithmetic and the three-index enumeration were proved by
  kernel decide with explicit equalities. No native_decide is used. Do not
  assume norm_num alone will normalize every ZMod index below an arbitrary P.

No author response or literature input was needed for this geometric clause.
