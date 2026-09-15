# Relative general position after event-centre sets

Source: reference/SM/sm-1-polygons.tex1489–1558. Do not restart the already
reviewed cube/path/germ/smooth-graph construction. All279 SM files are frozen.
The external SingleControlCenters prototype passed root68224; its independent
review and exact scoped evidence verifier passed (trace85577 terminal0). It proves the exact named-control/actual centre-set dichotomy.
Port its exact body into a NEW module and bind that port normally.

Next prove the finite cyclic index classification for any three-element support.
A simple proof avoids introducing an adjacency-count definition: if NoConsecutive
holds, use C. Otherwise choose a and a+1 in the support, then its distinct third
member M. The support is exactly contactSupport M a. If M=a-1, it is turnSupport a;
if M=a+2, it is turnSupport (a+1). In the remaining case ContactSeparated M a
holds by its four explicit inequalities. This gives the exhaustive combinatorial
cases directly. Use existing contactSupport_successive and wallCenterKind_unique
for disjointness only AFTER proving the actual wall predicates.

Do not re-prove the regular triangle obstruction from scratch. Frozen
SM.RegularTriangle supplies regular_triangle_det_ne_zero and triangle_turn_det.
At n=3, a three-element point-zero support is the whole occurrence set; its chi
zero at 0,1,2 contradicts that determinant. At n>=4, the actual consecutive triple
is collinear and collision-free. An exterior middle point gives a CuspCase by
collinear_exterior_cases; frozen cusp_not_regular excludes it. Endpoint equality
is excluded by collision freedom, leaving strict betweenness and F.

For separated contact supports, parameterize the actual collinear M on the base
line using scalar_of_det_zero or edgeLine_parameter_of_det_zero. Collision freedom
excludes parameters0,1. An interior parameter gives V, an exterior parameter E.
The other neighbour heights are nonzero by chi_nonzero_outside_singleton and the
ContactSeparated index facts. Their two nonzero signs determine bigon/sliding.
Transfer the named control sign change to the actual oriented determinant using
vertexControlNameOf_coverage (a sign change is invariant under overall negation).
For NoConsecutive, perform the same orientation transfer to obtain C.

For edge controls, use the already proved exact active concurrence singleton;
never classify a generic inactive T root. Actual pairwise crossing parameters
come from G1 and existing crossing persistence. Prove the source identity
T_efg = -(t_ef-t_eg)*H_ef*H_eg from the actual edgeLineRow/concurrenceDet formulas
and edgePoint line equations, rather than changing the control polynomial.
Continuity makes both nonzero H factors retain sign near the centre. Shrink the
germ if required, preserving its exact global path correspondence. Transfer the
named T sign change via edgeControlNameOf_coverage, then cyclically permute the
three actual labels to obtain all three crossing-order changes. Source labels,
actual centre and actual time must stay the same throughout.

The event certificate exposes other-control nonvanishing only at its centre.
For local persistence use continuity and a smaller positive common radius, or a
new theorem exposing the previously proved CentralRootPatch product condition.
Do not infer whole-radius facts from an implementation hidden behind an existential.

Finally assemble one actual piecewise-affine path with exact labelled endpoints,
strict synchronous Euclidean approximation, Regular membership, collision freedom,
finite nongeneric times, isolated simple germs and the exhaustive six noncusp
branches. Existing uniqueness of kinds assumes Simple, so it cannot supply this
existence proof. Only full source assembly plus independent review accepts
thm:relgp; then continue the corner laws, soft theorem and unconditional R.
