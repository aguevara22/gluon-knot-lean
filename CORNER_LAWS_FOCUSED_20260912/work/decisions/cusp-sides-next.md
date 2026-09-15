> COMPLETE: the full original cusp lemma passed independent review in
> reviews/lem-cusp-sides.json after audit042. The final acceptance-map audit is
> checkpoint043. Do not redo this plan; continue children-after-cusp.md.

# Next full geometric source claim: lem:cusp-sides

PARTIALLY IMPLEMENTED PLAN. Source: reference/SM/sm-1-polygons.tex:1024–1225,
with the K predicate at 718–730. The full F/V/T/E/C named-wall lemma is now
independently accepted. Preserve all four cusp source clauses; an empty or
unthreaded cusp is not the general case. Nine modules now prove the local crossing/needle geometry on one common radius; see cusp-after-local041.md for the exact remaining obligations.

## Centre, two cases and crossing/turn signs

1. Define CuspAt j using the actual germ, source n>=4, singleton turn support,
   empty remote-concurrence set, actual collinearity and exterior membership
   of vertex j relative to the closed segment between j-1 and j+1, and actual
   turn SignChanges. Do not assume the centre Regular: it has an antiparallel
   pair. SinglePointTriple already gives distinct vertices and nonzero edges.
2. Prove exactly one strict betweenness case. A has vertex j+1 between j-1
   and j, pair (f,g)=(j-1,j+1), corners (j,j+1). B has vertex j-1 between j
   and j+1, pair (j-2,j), corners (j-1,j). Cover every cyclic index and n=4.
3. Prove actual Delta at the selected pair is nonzero from the unique zero
   point triple. FlatIndices already classifies every nonincident edge/vertex
   incidence for that turn support, without assuming positive-flat geometry.
   Reuse its index proof and SingleTripleTransverse; do not redo them.
4. Prove the two actual line-intersection formulas. In A the outgoing leg
   parameter is -T/Delta; in B the incoming-leg distance from its final
   endpoint is -T/Delta. The parameter on the other segment tends to a strict
   interior coefficient. Continuity makes that parameter interior and the
   endpoint distance have absolute value below one. This second finite-segment
   condition is necessary. Crossing is exactly opposite signs of T and Delta.
5. Every other crossing support is unchanged. The only two pairs whose endpoint
   tests use the critical support are {j-1,j+1} and {j-2,j}. The unused one is
   actually compact-disjoint at the centre in its respective case. All other
   tests retain their nonzero signs. Do not assert unchanged thread order.
6. Prove each non-j needle determinant is a strictly negative multiple of
   central Delta, with that sign retained nearby. Combine it with the actual
   crossing/turn sign test for both needle-turn clauses. Only after proving
   exactly one crossing side define loop and no-loop sides; they cannot be
   chosen by assuming the desired side uniqueness. Use connected Generic side
   constancy for independent evaluation parameters.

## Actual short traversal arc and empty case

7. On the loop side construct the two actual newborn visits. Its oriented
   short arc is a terminal portion of f, the complete edge f+1, and an initial
   portion of g=f+2. Prove this using the half-open traversal circle and its
   actual evaluation, including wraparound. Its only polygon vertices are the
   two stated corners. Do not replace this with an arbitrary supplied arc.
8. For every other visit inside that open arc, prove its actual paired visit
   lies in the complementary arc. Three consecutive edges contain no other
   crossing with both visits there: adjacent edges do not cross on Generic
   tuples, and the nonadjacent pair has a unique actual intersection.
9. Define cyclic adjacency in the complete actual Gauss word, including the
   wraparound pair and the two-visit-only case. If one complementary open arc
   is empty, step 8 forces the particular short arc to be empty. Therefore the
   whole middle edge has no crossing on the loop side. It is absent from the
   newborn support, so full support persistence gives no crossing on the other
   side. A general cusp may have threads; never insert empty as a premise.

## Principal-turn rotation jump

10. Reuse RotationNumber/RotationContinuity for integrality and constancy on
    each connected Generic side. All non-j central turns are nonzero, so their
    actual principal angles have a common limit across the centre. Only the
    corner at j approaches the negative real-axis cut of Complex.arg.
11. The pinned Mathlib file Analysis/SpecialFunctions/Complex/Arg.lean supplies
    tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero and
    tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero. Inspect their exact
    types before using them. cornerRotor_re/im identify real part with the
    actual dot product and imaginary part with T. Prove the rotor tends to a
    nonzero negative real value and the correct side maps into each half-plane.
    An alternative uses the proved arg_of_im_pos/arg_of_im_neg arccos formulas.
12. Sum the finitely many limits, isolate j and subtract the two constant side
    sums. Divide by the nonzero 2*pi to obtain exactly rot(loop)-rot(no)=the
    loop turn sign, with sign in {-1,1}. Do not assign source rotation to the
    singular centre or assume differentiability of the germ.

Assemble all four clauses on a common radius and obtain full independent
source/type/body review before accepting the original row. Full def:walls also
needs the remaining F/V/K side conventions, centre classification, mutual
exclusivity and cyclic transport; its partial predicates do not accept it.
