# Completed — full flat-side geometry accepted

All work in the earlier plan below is now implemented and independently reviewed.
SM.flat_sides covers every source clause and one common interval. Candidate036
and final accepted-metadata037 passed; reviews/lem-flat-sides.json binds 91
supporting files. Original proof count is now10/132 (7.58%). No new literature
axiom was used. Do not redo this plan; next work is specified in
named-wall-sides-next.md. The original source remains unchanged.

The remainder is the historical implementation rationale, preserved for review.

# Remaining flat-side cyclic transport after checkpoint034 candidate

UNPROVED PLAN. Full lem:flat-sides remains pending/unmapped. The fourteen new
deletion/fusion modules compile. They prove actual deletion, Generic of the
central deletion, nearby Generic/chamber membership, crossing and visit
bijections, point/support/pairing preservation, exact parameter formulas,
determinant signs, within-piece order, and first-piece-before-second-piece order.
Global cyclic order and independently formed Gauss-word transport still need
proofs. The earlier flat-deletion-next.md describes the source scope, but its
construction/Generic/bijection/chamber steps are now implemented.

## Update after the FusionKey implementation

SM/FusionKey.lean now implements the scalar compression, exact actual-key
formula and GLOBAL cyclic visit-order equivalence described below. Its complete
development file compiled with exit0 before integration; audit035 passed (1413 local declarations; source row still pending).
The earlier sections are retained as the proof rationale. Next implement the
complete sorted-list rotation/word transport, any required interlacement
transport, and full source assembly. Do not redo the proved key calculations.

## Prove one scalar compression formula

For parent size n+1 and child n>=3, put c=(n:Real)-1 and choose the SAME strict
subdivision parameter r from hb.2, retaining hb itself. Define an increasing
piecewise affine real function:

```
F(c,r,x) = x                              if x < c
         = c + r*(x-c)                    if c <= x < c+1
         = c + r + (1-r)*(x-(c+1))       if c+1 <= x.
```

Prove StrictMono for 0<r<1 on all real x. A useful intermediate is the bend
`B(c,r,x) = if x<c then x else c+r*(x-c)`. For B, both-right comparisons use
the positive slope r, and cross-boundary comparisons use r*(y-c)>=0.
For F, use B below c+1 and the positive-slope 1-r branch above it.
B(c,r,c+1)=c+r supplies the exact boundary value, so comparisons across the
second boundary follow from strict monotonicity below and nonnegative offset
above. Prove formulas on all three regions including boundary equalities.

## Relate compression to ACTUAL visit keys

Let hP be the proved flat CrossingGeometry, Q=deleteVertex P j, hQ its proved
Generic geometry, and e=fusionVisitEquiv. Prove for every actual parent visit v:

```
geometricVisitKey hQ (e v) =
  F(c,r, traversalKey (traversalShift (j+1) (geometricVisitPosition hP v))).
```

This avoids applying Generic-only GaussRelabel to the flat centre. The existing
traversalShift and traversalBetween_shift are defined and proved for ALL actual
half-open traversal points, so no new geometric shift hypothesis is needed.

The three edge-label cases are concrete:
- Old edge j: its shifted label is -1 in ZMod(n+1), with natural value n.
  Its fused label is -1 in ZMod n, with real natural value n-1. Actual parameter
  t lies in (0,1) and becomes r+(1-r)*t, exactly the third region of F.
- Old edge j-1: shifted label insertIndex(-1:ZMod n), natural value n-1;
  fused parameter r*t gives the middle region. Recover this shifted label
  from deletionIndex_last, or from deletionIndex_fusionIndex in the retained
  case. insertIndex_val preserves its actual numerical representative.
- All other edges: deletionIndex_fusionIndex recovers the original label and
  fusionIndex_ne_last says the child label is not last. Its natural value plus
  one is strictly below n; prove this using val_injective, val_lt and
  last_index_val_succ, then cast explicitly. The unchanged actual parameter
  places its key strictly below c, and F is the identity there.

Use visitParameter_fusion for actual parameters and fusionVisit_edge for labels.
The cast of last_index_val_succ yields `((-1:ZMod n).val:Real)=n-1`.
Keep n=3 and all wraparound labels; no interior cut may be assumed away.

## Derive global order and independent word equality

StrictMono F reflects and preserves all strict/weak key comparisons. The actual
three-comparison definition of traversalBetween therefore transfers through e
to the shifted parent traversal order. traversalBetween_shift then proves
preservation of the original cyclic order. This is the missing global assertion;
the already proved within-edge parameter order alone does not replace it.

For complete lists, the visit equivalence proves permutation of the full sorted
finite visit universes, including the empty crossing case. Extend the proved
sorted_map_cut_rotation lemma to allow one strictly increasing outer function F
after its existing exact cut formula. Its finite lo/hi filtering proof can be
reused: apply F.monotone to every comparison of cut keys, and use actual target
key injectivity for independently sorted list equality. Do not define the
target list to be a chosen rotation. Exact cut keys come from the existing
traversalKey_shift formula; their original bounds come from the actual traversal
points. The result is actual IsRotated between the mapped full parent list and
the independently constructed child list.

Map Sigma.fst through that rotation and use fusionVisit_crossing to prove
geometricGaussWord transport under fusionCrossingEquiv. Transport alternating
four-visit interlacement using the proved cyclic-between equivalence and actual
two-visit fibre equivalences, following GeometricInterlacement's existing pattern.

## Full source assembly and acceptance

Combine FlatLocal, central generic_deleteVertex, actual crossing/visit/word
transport, signs and DeletionChamber on ONE radius (finite minimum/intersection).
Explicitly include the source's actual crossing geometry clauses, not merely
equal word values. In particular output actual interior/transverse crossings,
distinct crossing points, and no crossing point equal to ANY vertex. For the
last assertion use flat_nonincident_vertex_exclusion at zero and the actual
G1 exclusion off zero, together with edgePoint injectivity for the incident
endpoint cases. Do not presume GeometricRecordsAgree alone states this spatial
condition. Use the source sign change via the actual turn sign cast to Real
and WallGerm.SignChanges (or a proved equivalent determinant condition).
Retain the printed sign-change condition in the full source
statement, even though these geometric ingredients do not need it. Bridge to
every raw continuous source curve using pointZeroCurveGerm. The n+1/child-size
presentation covers all parent N>=4; prove/review the arithmetic reindexing if
the final aggregate uses N rather than n+1.

Only after all clauses and independent full source/type/body review may the
original lem:flat-sides map row be accepted. No partial review or helper modules
increase the fixed original 132-proof denominator. The main targets remain open.
