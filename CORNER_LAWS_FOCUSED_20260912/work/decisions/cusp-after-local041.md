> COMPLETE: the full original cusp lemma passed independent review in
> reviews/lem-cusp-sides.json after audit042. The final acceptance-map audit is
> checkpoint043. Do not redo this plan; continue children-after-cusp.md.

# Resume after cusp local geometry — checkpoint041

The nine new modules CuspBetweenness, CuspDefinition, CuspCenter,
CuspParameters, CuspCrossing, CuspNeedle, CuspUnusedPair, CuspOtherCrossings and
CuspLocal compile. The whole audit041 passed (185 SM modules, 1805 local
declarations). They are partial support only: original lem:cusp-sides remains
pending/unmapped, and original proof progress stays 11/132 (8.33%).

## Available proved results

- WallGerm.CuspAt is the exact source domain. cusp_case_existsUnique derives
  exactly one Bool case: true=A, false=B. The source bound is n>=4.
- cuspFirst/Last/Corner₁/Corner₂ have the source indices. Last=First+2.
  cusp_delta_ne_zero and cusp_newborn_remote include n=4 and cyclic wrap.
- cuspEndpointDistance is the g parameter in A and 1 minus the f parameter
  in B. cusp_distance_formula proves -T/Delta. The other actual parameter is
  strictly interior at the centre and stays interior nearby; distance is zero
  centrally and has absolute value below one nearby.
- cusp_crossing_iff_turn proves the actual selected pair crosses iff the
  actual turn is minus sign(Delta). Both finite-segment conditions are proved.
- cusp_needle_patterns proves the crossing-side equal turns and the
  noncrossing-side opposite turns. The central nonsingular needle determinant
  is a strictly negative multiple of Delta in both source cases.
- cusp_unused_disjoint_persists proves the other candidate pair is actually
  compact-disjoint nearby. cusp_other_crossings_equal compares every other
  unordered support for arbitrary G1 tuples satisfying proved local control.
- WallGerm.cusp_local_geometry combines all these on one positive radius,
  including Delta at zero and independently chosen punctured parameters.
  It does not use the source SignChanges hypothesis yet; that is needed next.

## Next executable step: prove and name the two actual sides

1. Use g.cusp_local_control h hc to obtain radius delta, and the actual
   h.2.2.2.2 SignChanges witness to obtain radius eta. Choose one common
   positive sample t0=min(delta,eta)/2 in g.SideParameter. Do not ask the
   author to pick a case, orientation or evaluation parameter.
2. Prove the elementary SignType fact: a negative product of the two real
   casts gives opposite nonzero signs (all SignType cases are finite). Together
   with the local crossing iff and nonzero Delta this proves exactly one of
   the positive/negative samples has the selected crossing. Also derive the
   explicit no-crossing iff turn=sign(Delta), not merely a negated crossing iff.
3. generic_family_crossing_constant and generic_family_chi_constant in
   SM.ChamberPaths extend the sample facts through each genuine connected
   Generic half-interval. turn is the actual chi at (j-1,j,j+1), so turn
   constancy needs no new topological axiom. Compare independent side parameters.
4. Define the unique loop Bool only after proving that unique crossing side;
   the other Bool is the no-loop side. A source-faithful definition may select
   by the actual sideBase crossing with its proved equivalence. Delta sign is
   controlled only near the centre: do not assert its nonvanishing on the
   entire original germ interval. Extend crossing/turn patterns by side
   constancy, while retaining the actual local Delta radius.

## Actual short arc and threads

5. Construct the two actual newborn visits using SM.PairVisits/pairVisit and
   isCrossing_pair_reverse, with their actual visitPosition parameters in (0,1).
   For f=cuspFirst and g=f+2, prove traversalBetween from f to g is exactly:
   edge f with parameter greater than its newborn parameter, all of edge f+1,
   or edge g with parameter below its newborn parameter. The traversal is the
   half-open ZMod n x Ico(0,1) space, not an arbitrary supplied interval.
6. Normalize with traversalBetween_shift f (SM.TraversalRelabel): shifted
   endpoint edges are 0 and 2 and the full middle edge is 1. n>=4 makes their
   actual residues distinct. Prove the normalized key inequalities and then
   transport back; this handles all wraparound cases without deleting n=4.
   traversalEvaluation_shift preserves actual evaluation. Parameter-zero
   points in the arc are exactly the two source polygon vertices f+1,f+2.
7. Any other crossing visit in the short arc has its actual partner in the
   complementary open arc. Both visits inside would place its two remote
   edges among f,f+1,f+2; the only remote pair there is {f,f+2}, so it would
   be the newborn crossing. Use crossing_visits_exhaust/other_visit and
   traversalBetween_complement for the actual partner, not an assumed pairing.
8. Define adjacency of the two newborn visits in the complete gaussList modulo
   its length, and prove equivalence to cyclic adjacency in the actual Gauss
   word (both occurrences are exhausted by the proved two-visit fibre). Include
   wraparound and the two-visit-only list. Adjacency implies one of the two
   complementary open arcs has no visit. Step7 forces this particular short
   arc empty. Its complete middle edge then has no crossing on the loop side;
   the edge is in neither newborn member, so support persistence gives the
   same on the no-loop side. Never assume the general cusp is unthreaded.

## Signed rotation jump and final assembly

9. Reuse rotationNumber_integer and rotationNumber_family_constant on each
   connected Generic side. cusp_other_turn_regular proves every non-j
   principal angle has the same central limit via continuousAt_principalAngle.
10. cusp_rotor_negative_real identifies the unique antiparallel corner.
    Mathlib Analysis/SpecialFunctions/Complex/Arg.lean:599–636 supplies
    tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero and
    tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero. Actual cornerRotor.im
    is T, so the proved side signs select -pi and +pi limits. Keep filters and
    continuity on the germ's actual interval; no derivative is assumed.
11. Sum finitely many limits, cancel all non-j terms, and divide by nonzero
    2*pi. Prove exactly rotation(loop)-rotation(no)=turn(loop), with that sign
    in {-1,1}. Do not assign source rotation to the singular centre.
12. Assemble every printed clause of sm-1-polygons.tex:1024–1225 on a common
    radius and obtain full independent source/type/body review before mapping
    or accepting the original row. Full def:walls also stays pending until
    remaining conventions, exclusivity, centre classification and cyclic
    transport are proved. Helpers and partial clauses never increase counts.
