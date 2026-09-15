# Finish the actual cyclic Gauss-word clauses

Checkpoint089 adds59 checked candidate declarations. The soft family is now
proved Generic on one positive interval and lies in one actual labelled and
quotient chamber. Every enlarged crossing support is classified: the injective
image of a parent crossing, or the incoming/return support exactly in the loop
sector. The newborn support cannot equal an inherited one. Inherited parameter
and point limits, direction signs and finite visit order are proved. Newborn
parameters tend to1 and0 and its point toPj; in the loop sector these are the
actual crossing data. All incoming inherited parameters lie before the newborn,
and all return inherited parameters lie after it, on one common interval.

These are frozen candidates, not accepted source rows. Full lem:soft-generic
still needs actual Cycle/Gauss transport, oriented newborn adjacency, deletion,
and one assembly containing all four printed clauses. Then continue thm:A-soft
and the corner soft theorem; the ultimate goal remains corner wall laws and soft.

## Concrete next proofs

1. Intersect the finitely many proved radii/neighborhoods needed below. Include
   all parent crossing parameters and direction signs, all inherited visit
   comparisons, Generic/chamber, the support classification, both newborn
   parameter identifications, and both visit windows. Preserve the full parent
   Generic/admissible/arbitrary-j source domain. Radius shrinking must retain
   the actual chamber conclusion, for instance by keeping its original midpoint
   as a fixed chamber base even when the final radius becomes smaller.
2. Define the actual inherited crossing map using the Finset.image of
   softParentEdge j. Prove it lands in Crossing Q from the classification,
   is injective by Finset.image_injective, and has image precisely the inherited
   supports. For a non-loop sector it is a bijection. In the loop sector its
   image excludes exactly the proved newborn crossing. Do not introduce freely
   chosen labels or an assumed crossing bijection.
3. Lift the map to actual Visit values by mapping the edge membership witness.
   Prove injectivity, the crossing pairing, the edge formula, exhaustive
   inherited visits and identification with canonical crossingParameter. Under
   Generic, these parameter values are exactly the visitParameter values.
4. Prove order preservation of inherited visits from the physical edge
   insertion and same-edge parameter order. First investigate the explicit
   arithmetic candidate below: sending parent j to the return edge may preserve
   the existing numerical cut exactly, making filtered gaussList equality
   available. The canonical gaussList sorts traversalKey using ZMod.val, whereas
   the source insertion uses physical labels1,...,n. Do not presume a literal
   list equality until that arithmetic is proved, including insertion after
   source label n (residue0) and the empty parent crossing set. If necessary,
   prove rotation equivalence with a correctly chosen cut. Permutation alone
   does not prove cyclic order.
5. In the non-loop case prove the actual gaussCycle map identity, then the
   gaussWord identity by mapping Sigma.fst. In the loop case remove both visits
   of the actual newborn and prove the remaining cyclic sequence is precisely
   the mapped parent cycle. Its crossing-labelled word must agree as well.
   If Cycle filtering is not already available, construct it by the rotation
   quotient and prove List filtering respects IsRotated; do not assume an API.
6. Use the checked incoming/return parameter windows, complete crossing
   classification and soft-edge exclusion to prove no actual visit lies on the
   oriented traversal arc from the newborn incoming visit through Pj and the
   inserted vertex to the newborn return visit. Prove the actual
   nextGaussVisit incoming = return, retaining orientation and cyclic wrap.
   The existing gauss_next_no_visit_between proves the opposite direction;
   derive the needed converse with distinct visits or a concrete rotated list.
7. Assemble all source clauses of lem:soft-generic, with one epsilon0, actual
   Generic/chambers, all turn/direction statements, full inherited crossing
   convergence/order/signs and both sector Gauss conclusions. Only this complete
   result can be queued as the full source lemma, still pending stronger review.

## Exact existing interfaces

- SoftParentEdges: literal parent-edge injection, exhaustive non-soft image,
  successor criterion and full affine edgePoint discrepancy.
- SoftInheritedParameters: actual canonical edgeParameter limits, supporting
  softInheritedPoint limit, strict persistence, direction sign, and identification
  with canonical crossingPoint under derived child G1.
- SoftParentPairStability: every remote parent pair keeps crossing status, with
  disjoint parallel pairs included; all inherited same-edge comparisons persist.
- SoftCrossingClassification: soft_crossing_support_classification and
  soft_newborn_support_not_inherited, covering all enlarged labels and sectors.
- SoftNewbornParameters: values/limits1,0,Pj and actual loop crossing data.
- SoftNewbornVisitWindows: both strict windows, then finite common radius.
- SoftFamilyG2: Generic, G2 and actual chamber on a positive interval. Its proof
  uses compact closed-triple persistence, with no Generic premise at epsilon0.
- Frozen088 SoftAttachmentSigns, SoftFamilyTurns and SoftEdgeAvoidance supply
  the remaining exact insertion, turn, direction and endpoint-contact clauses.

Canonical examples: SM.FusionVisits builds actual visit equivalences and pairing;
SM.FusionGaussWord proves rotation when arity/cuts change, but its fusion
hypotheses do not apply to soft insertion. SM.GaussWord gives gaussList,
gaussCycle and gaussWord as the actual sort and rotation quotient.
SM.GaussCyclicGap defines nextGaussVisit and GaussVisitsAdjacent.
Read exact theorem types before reuse; a fixed-arity generic-family transport
does not directly compare this parent to its child.

UNFORMALIZED ARITHMETIC CANDIDATE for the immediate next proof:
the value of softParentEdge j k should be k.val when j.val=0 or k.val<j.val,
and k.val+1 otherwise. Derivation to check in Lean: when j=0 (last physical
vertex), the return edge has enlarged residue0 and every other parent edge
retains its label. When j is nonzero, old residue0 maps to enlarged residue0,
labels strictly before j retain their values, and j and every later old label
move up by one because j now denotes the return edge. This suggests the map
is strictly increasing in ZMod.val for every j, including the seam. If proved,
different-edge inherited visits retain ordinary sorted order; same-edge order
is already checked. Then a nodup sorted-list argument should prove equality
of the filtered child gaussList with the mapped parent gaussList, before
passing to Cycle. This is a proposed next argument, not a checked declaration.

Root owns one kernel/build/audit at a time; reviewers none. Preserve every
failed body/prototype/log before repair, freeze passing files and keep the
canonical327 modules, map and sources unchanged. Review authorship and strategy
contributions must be disclosed. Same-model technical review does not grant
stronger statement/definition fidelity or source acceptance. Accepted source
proofs remain19/132. Keep progress reports and resumable checkpoints active.
