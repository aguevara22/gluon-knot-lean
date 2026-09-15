# Actual flat deletion — next proof after checkpoint033

UNPROVED IMPLEMENTATION PLAN. This is not a source claim or proof receipt.
The local central geometry and nearby geometric records now compile in
SM.FlatLocal. Full lem:flat-sides remains pending and unmapped.

## Construct the actual deletion

Write the parent size as n+1 with n>=3; derive this representation from every
source size N>=4 using n=N-1. Define the child labelled tuple by
`deleteVertex P j i := P (insertIndex i + (j+1))`.
It begins at the old successor of j, omits exactly vertex j, and retains the
induced cyclic order. Prove index injectivity, exclusion of j, and exhaustion
of all other parent labels using InsertionIndices, including the closing edge.
Every child edge except index -1 is inherited; its closing edge is exactly
`P (j+1) - P (j-1)`. Coordinate reindexing proves continuity of deletion.

StrictBetween gives a unique lambda in (0,1). Prove on ALL parent labels that
`shift (j+1) P = appendVertex (deleteVertex P j) lambda` using
insertion_indices_exhaust and the actual affine fusion equation. This is an
inverse construction of deletion, not an arbitrary tuple or assumed bijection.

## Prove the deleted tuple Generic

G1: distinct child labels give distinct retained parent labels. A zero chi
would have the parent's unique zero support {j-1,j,j+1}, which contains j.
The deletion image excludes j, a contradiction. Betweenness is not needed
for this part.

G2: every unchanged child interior is an actual parent interior. On the fused
edge, a parameter q<lambda belongs to the first old segment at q/lambda;
q>lambda belongs to the second at (q-lambda)/(1-lambda). Parameter q=lambda
is the deleted vertex. No other child edge contains that vertex, by the proved
flat_nonincident_vertex_exclusion. Thus three distinct child edge interiors
meeting would give three distinct parent interiors meeting, contradicting
flat_center_g2. Prove each membership, label relation and strict inequality;
retain the boundary child size n=3.

## Construct crossing and visit correspondences

The parent edge map fuses j-1 and j to child edge -1. A parent remote crossing
cannot use both split edges since they are adjacent. Its actual point belongs
to both corresponding child interiors. Child G1 then proves remoteness, rather
than assuming exceptional remote pairs survive deletion. Conversely a child
crossing on the fused edge has parameter unequal to lambda, so the actual point
chooses exactly one split segment. flat_common_interiors_remote proves parent
remoteness. Prove inverse laws or injectivity by actual crossing-point uniqueness
and crossingPoint_injective_of_geometry; no crossing bijection is an input.

All inherited edge factors are positive (1, lambda or 1-lambda), so the actual
determinant sign is preserved. The fused visit parameters are lambda*a on the
first piece and lambda+(1-lambda)*b on the second. Prove every first-piece visit
precedes every second-piece visit and all orders within pieces are preserved.
Use these actual visits to transport the cyclic word, pairing and interlacement.

## Account for the cyclic cut

The child's chosen cut is j+1, while the original parent list starts at 0.
Generic-only GaussRelabel cannot be used at the flat centre. Prove cyclic
equivariance for CrossingGeometry first, either by extending the actual
parameter/visit/SortedCut proof, or by a fully proved generic-density argument
with simultaneous local record stability and commuting canonical transports.
The direct extension is the initial approach; the alternative remains unproved.
Do not identify distinct sorted lists without proving the cyclic transport.

## Nearby deletion chamber and full assembly

Apply openness of the genuine Generic locus to the proved central deletion
and the continuous deletion curve. Choose one smaller full interval, including
zero, whose deleted tuples are all Generic. Its connected image lies in the
actual central connected-component chamber; prove the labelled and quotient
statements with the existing chamber definitions. Do not substitute path
components or merely prove the two endpoints are Generic.

Assemble every printed clause of lem:flat-sides on one common radius and bridge
back to every raw source curve. Preserve the printed sign-change condition in
the complete source theorem even though local geometric helpers do not use it.
Request independent complete statement/definition/body review before accepting
the original row. No helpers or partial clauses increment the 132-proof count.
