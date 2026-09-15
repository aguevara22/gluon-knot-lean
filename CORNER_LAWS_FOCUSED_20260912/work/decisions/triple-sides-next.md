# Next full proof: lem:triple-sides

UNPROVED IMPLEMENTATION PLAN. Source sm-1-polygons.tex lines 670-709.
Target domain is every actual WallGerm with pointZeros empty and concurrences
exactly the singleton support {e,f,g}. Do not add a sign-change, derivative,
transversality-of-parameter, named T-wall or Regular premise. The source's
n>=3 polygon domain remains explicit. The singleton concurrence membership
itself proves that the three labels are distinct and pairwise remote.

1. Use WallGerm.pointZeros_empty_iff for G1 at the actual centre. Extract the
   common point and pairwise remoteness from mem_concurrences. Use G1 remote
   meeting to prove the three actual central crossings and their nonzero
   direction determinants. Every selected central pair has that same unique
   point. Prove equal edgeParameter values along each selected edge using
   crossingPoint_unique, crossingParameter_spec and
   crossingParameter_eq_edgeParameter. The latter only needs G1, so it is
   valid at the triple centre even though G2 fails.

2. Establish one actual neighbourhood with fixed complete crossing support.
   A possible route is finite G1/chirotope stability: g1_persists gives G1,
   each nonzero real determinant has locally constant SignType sign, and
   the finite intersection over all distinct vertex triples preserves every
   chi. Repeated triples have identically zero chi. crossing_iff_of_chi_eq
   then preserves every actual IsCrossing support in both directions.
   Alternatively use wall_segment_stability and the G1 disjoint/interior
   dichotomy. No central Generic premise is allowed. Compose these proven
   neighbourhood results with the actual continuous germ curve.

3. For every central crossing {e,h} with h outside {e,f,g}, prove its actual
   parameter on e differs from the central triple parameter. If equal, the
   unique point of {e,h} equals the selected common point, putting it in h's
   relative interior. G1 then makes h and f remote, giving the distinct
   concurrence triple {e,f,h}; this contradicts the exact singleton Z_c.
   Handle all other-edge indices, not just crossings selected in advance.
   Repeat by permutations for f and g. The actual finite central crossing
   support lets all exclusions be combined in one neighbourhood.

4. Every relevant edgeParameter is continuous near the centre because the
   actual Cramer denominator is nonzero there (continuousAt_cramerFirst and
   crossing_edgeParameter_det_ne_zero). The selected pair parameters agree
   at the centre. Each third crossing parameter is either strictly below
   their common value or strictly above it. Preserve its strict comparison
   with BOTH selected parameters. This direct finite-neighbourhood argument
   replaces the printed subsequence argument without weakening the result.
   It proves no third actual crossing visit lies strictly between the two
   selected visits, in either order, on any of the three edges.

5. At every punctured parameter, g.generic_punctured supplies full G1/G2.
   generic_crossingPoint_injective gives distinct actual selected crossing
   points, after proving their support Finsets distinct. All three selected
   crossings persist. Connect the no-between condition to actual adjacency
   among visits on that edge. Existing Visit/visitParameter/visitPosition
   are geometric; crossingParameter_eq_edgeParameter is the required bridge.
   If using an ordered-list or CovBy encoding of adjacency, prove its
   equivalence to the accepted finite visit order rather than assuming a
   sorted-word conclusion or supplying an arbitrary list.

6. Convert the one neighbourhood of g.zeroParameter into one positive real
   radius delta <= g.radius, valid on BOTH punctured sides. Use the actual
   interval subtype topology; prove the radius/evaluation bridge. Preserve
   all three edge adjacency conclusions and the pairwise distinct crossing
   points together, with no side-specific hidden radius or premise.

Only the complete aggregate, after independent source/type/body review and
project audit, may accept the original PROVE row. Partial persistence or
adjacency helpers do not increment the original denominator. All work belongs
under work/; frozen references, blueprint and delivered ZIPs stay unchanged.


Pinned neighbourhood APIs inspected for step 6: Metric.mem_nhds_iff gives
an actual positive-radius ball contained in the eventual predicate set;
Metric.ball_mem_nhds gives the converse. Subtype.dist_eq identifies interval
subtype distance with real distance, and Real.dist_eq at zero is abs(t).
A proposed helper should prove the actual equivalence between an eventual
predicate at g.zeroParameter and a common 0<delta<=g.radius on all parameters
with abs(t.val)<delta. This helper is NOT YET IMPLEMENTED. It prevents a
side-specific or one-sided neighbourhood from silently replacing the printed
common punctured interval.
