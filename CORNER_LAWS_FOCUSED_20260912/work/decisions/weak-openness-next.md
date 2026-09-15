# Completed supporting proof — lem:weak-open

Completed and independently accepted on 2026-09-10. SM.weak_open proves all
three source clauses. Review: reviews/lem-weak-open.json. Development receipt:
checks/checkpoint-010-output.json (subsequent receipts also include it).
WeakGeometry and WeakTopology implement steps 1–4 below, PolygonalConnected
implements finite straight-segment chains, and EuclideanTuple supplies the
actual Euclidean coordinate homeomorphism and ball. WeakOpen assembles them.

Accounting correction: this source lemma is absent from the frozen focused
NODES.tsv, so it is an additional supporting row. It does not increase the
original 132-proof or 191-checklist baseline. The expanded checklist tool also
reports this extra row, with its larger denominator. Preserve both meanings.
The text below records the historical plan; its UNPROVED labels describe its
status when written, not the current accepted implementation.

SM/WeakGeneric.lean now defines every printed weak-genericity condition, proves
Generic implies WeakGeneric, and proves invariance under cyclic relabelling.
It defines the silent locus and both quotient and labelled visible chambers.
The openness, polygonal connectedness and ball assertions remain unproved.

## Available compiled ingredients

- GenericTopology: the common-point condition for three fixed closed segments
  is closed, by projection over the compact parameter cube.
- SegmentStability: disjoint actual closed segments stay disjoint nearby.
- WallSegmentStability: transverse interior intersections and their parameter
  orders persist simultaneously; both parameters are continuous on a common
  open neighborhood.
- Chambers: generic locus openness, actual quotient components and real
  parameter comparisons. Do not assume G1 for a merely weakly generic tuple.
- WeakGeneric: nonincident **closed-segment** vertex exclusion. It does not
  exclude vertices from entire supporting lines or disjoint collinear edges.

## Proof route (UNPROVED PLAN)

1. From nonzero turn determinants, prove that distinct adjacent edges meet only
   at their shared vertex and hence have disjoint relative interiors. Adapt the
   already proved g1_successive_intersection argument using the turn premise;
   do not introduce G1 as an extra hypothesis.
2. From nonincident vertex exclusion, a common point of remote closed segments
   has strictly interior parameters. The four endpoint cases contradict the
   relevant vertex-on-closed-segment prohibition. Full-line exclusion is not
   available and is unnecessary.
3. The weak base conditions and G2 then imply absence of common points of three
   pairwise remote closed segments, just as in the GenericTopology proof. The
   reverse direction only needs adjacent-interior exclusion. Reuse the closed
   triple condition to preserve these finitely many exclusions nearby.
4. Preserve the weak base conditions themselves: nonzero edge vectors and turn
   determinants by continuity; vertex/closed-segment exclusion by applying
   disjoint_segments_persist to the vertex as a zero-direction segment and the
   actual closed edge (the auxiliary lemma correctly allows zero directions);
   each remote pair either is
   centrally disjoint (use disjoint_segments_persist) or has nonzero determinant
   (preserve it and derive uniqueness). Disjoint parallel/collinear pairs must
   remain permitted. Intersect all finitely many neighborhoods.
5. Prove all remaining source clauses. An open subset of the finite real vector
   space has open, polygonally connected components. Ordinary path connectedness
   alone does not establish polygonal connectedness: define finite chains whose
   consecutive affine segments stay in the component and prove reachability is
   relatively clopen by small convex neighborhoods, as the source does.
6. Deliver the local ball assertion in the source's ambient real-coordinate
   topology. The existing Plane/product/Pi norm is a max norm, not the Euclidean
   norm. Either prove the requisite Euclidean comparison/homeomorphism or phrase
   and prove the actual sum-of-coordinate-squares ball inclusion. Do not silently
   substitute a different numerical norm in a source claim.

Current source lemma: reference/SM/sm-1-polygons.tex lines 279 onward, including
the end of its proof around line 345. All clauses need kernel proofs and an
independent source/type review before lem:weak-open is counted.

## Subsequent required branch: Gauss word and interlacement

def:gauss, def:interlace and def:visible are still pending. Use actual visits
(edge index, strict interior crossing parameter), traversed around the oriented
circle. Useful pinned APIs: Mathlib/Order/Circular(.lean and /ZMod.lean),
Mathlib/Data/List/Rotate.lean (List.IsRotated.setoid), and finite sorted lists.
The cyclic sequence must be independent of a chosen cut/starting label, and
the actual two visits per crossing and their parameter ordering must be proved.
Do not replace the Gauss word by an arbitrary supplied list or graph. These
definitions are prerequisites for the corner state sum and its laws.

The full focused scope, including R and the final wall/soft aggregate, remains
unchanged. These local foundations are not a substitute for those targets.
