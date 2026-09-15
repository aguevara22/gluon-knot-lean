# Remaining named-wall geometry after checkpoint038

COMPLETED: all localization, exact T exchanges and F/V/T/E/C assembly below are
implemented as SM.wall_sides and independently accepted. Candidate039 passed;
the full review is reviews/lem-wall-sides.json, SHA256
2dfb995b053b40092a740b00127e33524ab0b15b15a9bc1e5bd820ede26958ff.
The final acceptance-metadata audit040 passed. Do not redo this plan.
The next full source unit is cusp-sides-next.md. Full def:walls stays pending.

Historical implementation plan follows. Source:
reference/SM/sm-1-polygons.tex:710–750 and 896–1020. Full def:walls also remains
pending because its cusp, side-convention, exclusivity and cyclic clauses are
not yet implemented. Preserve every source hypothesis and conclusion.

Checkpoint038 compiled 162 SM modules and 1632 local declarations. Its twenty
new modules prove silent E/C geometry and the V support classification, persistent
parameter order and contact parameter limits. These are partial source work;
original counts remain 10/132 proofs and 23/191 checklist rows. Do not repeat
the completed proofs in named-wall-sides-next.md steps 1–5 or the accepted flat
result. No extra axiom, source weakening or original acceptance is authorized.

## A. Simultaneous V contact-neighbourhood and actual visit localization

1. Source VertexEdgeAt gives an actual central base parameter r strictly between
   0 and 1 with P M = edgePoint P a r. Persistent central supports mean actual
   IsCrossing AND not ContactAffected M a. At this centre raw IsCrossing includes
   two endpoint contacts, which must never be called transverse interior visits.
   ContactParameters proves actual interior geometry only for unaffected pairs.
2. ContactVertices.contact_parameter_ne_contact separates every persistent
   crossing parameter on base a from r. On leg M-1 persistent parameters lie
   strictly below endpoint 1; on leg M they lie strictly above endpoint 0.
   ContactVertices also excludes every vertex from every persistent crossing.
3. Form one finite set of the positive distances in step 2, together with
   positive values 1, r and 1-r. Its positive minimum gives a single eta>0,
   chosen small enough that all central distances exceed 4*eta and the base
   window stays inside (0,1). Including 1 handles the empty crossing universe.
   This is a proof plan: prove every membership and strict bound explicitly.
4. Use continuity of actual Cramer parameters at every persistent pair to find
   one neighbourhood where all these parameters move by less than eta. Combine
   ContactApproach.contact_parameters_approach at epsilon=eta: both changing
   pairs have their base parameters near r and leg parameters near 0 or 1.
   Finite intersections and triangle inequalities yield simultaneous separation.
5. Use ContactPersistence to turn any nearby unaffected crossing into one of
   the central persistent supports. This must cover every actual nearby visit,
   not only a selected list of central crossings. Identify actual crossing and
   visit parameters with the Cramer parameters on each punctured Generic tuple.
   Exhaust the actual edge labels a, M-1 and M. The windows contain all newborn
   visits and no other visits. ContactOrder supplies every persistent comparison
   outside the windows; no unjustified ordering inside a window is needed.
6. Assemble V regularity, noncritical chirotopes, spatial conclusions, exact
   support difference/bigon/sliding patterns, localization and order on ONE
   positive radius. Interpret contact parameter limits as actual visits only
   on the side where the corresponding finite segments really cross.

## B. Exact T exchanges

1. TripleAt gives actual central G1, one actual concurrence triple and sign
   changes of the three actual parameter differences. Reuse the accepted
   TripleSides theorem for the three persistent pairs, nearby point distinctness
   and adjacency of the two selected triangle visits on each triangle edge.
2. Prove central parameter-tie classification. Equal actual parameters on two
   distinct crossing partners give one common point in three actual interiors.
   G1 forces pairwise remoteness, so the singleton concurrence set forces the
   unordered edge triple to be exactly the distinguished triangle. Include all
   permutations. Equal partners give false strict comparisons on both sides.
3. Every other comparison is centrally distinct and persists by finite
   continuity. Combine the three source SignChanges conditions with the scalar
   implication from a negative product to opposite strict orders. Prove exactly
   the three selected exchanges, with all other comparisons fixed on one radius.
   Central triangle visits coincide: do not assume central G2, global
   CrossingGeometry or a unique central Generic word.

## C. Full source assembly and review

Reuse FlatLocal/FlatSpatial for F on every source N>=4, and SilentSides for E/C.
Avoid unnecessary parent/child dependent-type conversion through the stronger
full flat deletion theorem when only the wall geometry is required.

Assemble every F/V/T/E/C source clause with actual segments, points, visits and
source side domains. Verify that all uninvolved crossings and centrally distinct
comparisons are covered. Obtain independent full source/type/body review, bound
to audited current files and transparent definitions, before mapping and accepting
lem:wall-sides. Helpers and partial reviews add no original proof percentage.

The original shift source omission remains a separately reviewed local repair;
it does not prevent this work. No author answer is needed.
