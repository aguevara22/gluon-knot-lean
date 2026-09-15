# Weighted duplication after the concrete cut fibres

Author: `/root/review_mark_transport`. Source:
`reference/SM/sm-2-amplitude.tex:1217–1402`, especially the endpoint cases and
the three presentations. This is an implementation checkpoint and proof
outline, not a kernel receipt or source acceptance. The weighted statements
below remain to be proved in Lean. Check each current prototype receipt for
the separate candidate groups; no reviewer kernel is authorized.

The frozen `SoftDuplicationCutFibers` equivalence sends a complete child cut
set T to its actual collapsed finite image C and the local subset Q of cuts
over s. Expansion takes every nonduplicate preimage of C inside I and adds Q.
Its fibre predicate forces endpoint cuts and permits no extra preimages.
The actual transform has already been reindexed through this equivalence by
`SM.SoftDuplication.nearFarTransform_eq_cutFiber_sum`; every gate and child
product is retained in the summand.

## Fixed row conventions

For a strictly spanning interval I=[X,Y], write the core cut neighbors of s
as L<s<R, and put a=t(L), b=t(R), h=H0(X,s,Y). The row order in
`spanningRows` is deliberately explicit:

| Fin 3 row | Q | Exceptional child | Child multiplier |
|---|---|---|---|
| 0 | {A} | [A,old(R)] | (etaPlus-b)/2 |
| 1 | {B} | [old(L),B] | (etaMinus-a)/2 |
| 2 | {A,B} | [A,B], a singleton | 1 |

The printed source table places B-only before A-only; the implementation
places A-only first. The physical subset, not its numeric row number,
determines the corresponding scalar identity.

Each one-cut row has near value a at its duplicate cut: the neighboring
triple pulls back to (L,s,R), whose auxiliary core near value is t(L).
The two-cut row instead has near values a at A and b at B. Both duplicate
far entries equal h because the strictly spanning top endpoints lie outside
the pair. Thus the local gate products are:

| Row type | Ordinary top | Root top |
|---|---|---|
| A-only or B-only | (a-h)/2 | (a+h)/2 |
| Both | (a-h)(b-h)/4 | (a+h)(b+h)/4 |

Their child-weighted sum must equal k times the core local gate, where
k=(etaMinus+etaPlus)/2. This is the source residual calculation, using
a*a=1 and h*h=1. Do not divide by the core gate or any child value: either
may vanish. Root's scalar identities must be applied after extracting a
common product by proved factor transport.

If s is not a core cut, Q is empty and there is one presentation. Prove that
exactly one consecutive core child strictly spans s, including the unary
composition. Its expanded child has multiplier k. Every other child and top
gate must be transported without change.

## Endpoint rows

`startingRows` has I.left=A and B<I.right. Row 0 selects {A}; row 1 selects
{A,B}. In row 0 the first child has multiplier (etaPlus-t(U))/2, where U is
the first core cut after s. Row 1 contributes [A,B] and a new gate at B with
near value t(U) and far value t(I.right). Their ordinary and root local sums
are respectively (etaPlus-t(I.right))/2 and (etaPlus+t(I.right))/2.

`endingRows` has I.left<A and I.right=B. Row 0 selects {B}; row 1 selects
{A,B}. In row 0 the last child has multiplier (etaMinus-t(V))/2, where V is
the last core cut before s. Row 1 contributes [A,B] and a new gate at A with
near value t(V) and far value t(I.left). Their ordinary and root local sums
are respectively (etaMinus-t(I.left))/2 and (etaMinus+t(I.left))/2.

In those endpoint formulas, `t(I.left/right)` means t of the collapsed
physical endpoint, as in `ordinaryLift`; it is not t on a child `Fin (n+1)`.
Both endpoint rows exist even when the collapsed core interval has one leaf.
The actual singleton [A,B] transform has already been checked separately by
TransformSetup; it must not be sent to a zero-length core BoundaryInterval.

## Avoiding intervals and the next transport work

The `SoftDuplicationAvoiding` inverse is the full preimage of C restricted to
I, and collapse is injective on that entire closed interval. It covers an
interval ending at A and one starting at B. A global use of `old` alone is
incorrect in the latter case: old(s)=A lies outside that interval. Use the
proved actual preimage map, or establish compatibility with the alternate
increasing section `(A s).succAbove`, which sends s to B. The two increasing
sections agree away from s. This alternate-section compatibility is a next
proof obligation, not a theorem asserted by this note.

For every row, establish concrete bijections on all unaffected interior cuts
and consecutive child intervals. Use the canonical consecutive-cut APIs and
root's `CutSetNearFarNeighbors` characterization to identify actual near
neighbors, and the fixed outer endpoints for far triples. In particular,
the gate at L may have A or B as its right neighbor, and the gate at R may
have either as its left neighbor; collapsing that neighbor must recover the
same core triple. No cardinality calculation alone proves these identities.

After these weighted fibre identities, prove every ordinary coordinate is
E before invoking triangular inverse uniqueness. On a one-leaf collapsed
endpoint interval, the actual neighbor identity t(successor)=etaPlus or
t(predecessor)=etaMinus makes the ordinary multiplier zero. For the full
root interval, handle s=0 and s=last separately using the cyclic neighbor
values at the opposite linear endpoint. Only then restore geometric near
arrays through the already proved complete-transform freedom and establish
the actual rooted boundary-word correspondence.

No source row is accepted by these candidates or this note. At this
checkpoint source acceptance remains 19/132 (14.39%), expanded checklist
39/192 (20.31%), and final targets 0/8.
