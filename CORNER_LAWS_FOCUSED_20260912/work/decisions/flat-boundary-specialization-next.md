# Next executable work: specialize the checked integer response to a flat wall

The unordered source-domain integer response is now checked, and the physical
deletion-root map is checked in PhysicalDeletionRoots.body.lean. Reuse these
frozen candidates; do not redefine the accepted geometry or response. All remain
subject to stronger fidelity review and canonical integration.

Implement boundary positions for the three consecutive critical labels at an
arbitrary root, with source arity n >= 4. The following is an implementation
plan, not a claim that these remaining identifications have already been proved.

1. For a nonincident root g, obtain the actual boundary position k of j using
   boundaryIndex_surjective. Prove 0 < k.val and k.val + 1 < n: the excluded
   first and last positions would force g = j-1 or g = j. Construct the triple
   k-1,k,k+1; prove its actual labels are j-1,j,j+1, both gap lengths are one,
   and its span is proper. Fullness would force n=3. Uniqueness follows from
   IncreasingBoundaryTriple.vertexSet_injective.
2. For g=j-1, construct boundary positions 0,1,n-1; their labels must be j,j+1,
   j-1. Prove full span, a singleton left gap, and n-2 leaves on the right.
3. For g=j, construct positions 0,n-2,n-1; their labels must be j+1,j-1,j.
   Prove full span, n-2 leaves on the left, and a singleton right gap.

With StrictBetween obtain P(j)=P(j-1)+r*(P(j+1)-P(j-1)), 0<r<1 and distinct
endpoints. Valid affine coordinates in the three orders are respectively
(0,r,1), (r,1,0), and (1,0,r), with base P(j-1) and nonzero direction
P(j+1)-P(j-1). Prove the epsilon pairs (+,+), (-,+), and (+,-) directly.

The substantive remaining identification is geometric: the nonincident
contracted tuple, and the nonleaf gap tuple in each incident case, must equal
the actual deleted tuple up to a proved cyclic shift. Prove the pointwise
label equality and its physical root correspondence before using
treeCoefficient_shift. The endpoint map alone does not establish that tuple
equality. Existing fusionIndex_physical_deletion_root and the closing-root
facts for restricted/contracted words supply the root portion.

Finally, prove that the reversed far sign is minus the turn at j in all three
cyclic orders. The source right side has turn -1 and left side +1; these are
not necessarily the positive/negative time sides. Apply the fixed-sign integer
response with the correct subtraction order. Preserve independent sufficiently
close side points and the center-valued deletion coefficient.

This proves thm:A-S3 only after all branches and side-order cases are assembled.
No flat-law row, half-map row, corner law, or soft theorem is accepted by this
plan. Do not wait for author input.
