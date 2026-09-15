# Next source unit after fibres: def:germ

UNPROVED IMPLEMENTATION PLAN, not accepted mathematics. Source:
reference/SM/sm-1-polygons.tex lines 653-669. Preserve the frozen source.

Define an actual wall germ with positive radius, a continuous curve on the
open interval (-radius,radius), full Generic at every nonzero parameter,
and a nongeneric centre. Use the interval subtype so no global extension
of a locally defined source germ is silently required. Keep n>=3 explicit
where interpreting source polygons, and retain the actual tuple topology.

Construct the negative and positive side maps into GenericTuple n from the
actual half intervals. Prove continuity and preconnectedness of their images,
then membership in one actual connected component. Choose the actual points
at +/-radius/2 to name those components and prove independence of the chosen
point. Descend to the genuine GenericPolygon quotient with polygonProjection;
do not define a chamber as an arbitrary equivalence or assume path lifting.
Derive that any function constant on the actual chambers has a well-defined
side value. Existing Chambers/ChamberPaths/CyclicChambers supply genuine
connected components and continuity machinery.

Define Z_pt as the actual finite set of unordered three-element index sets
with vanishing central chirotope. Define Z_c as actual unordered triples of
pairwise remote edges with a common point in all three relative interiors.
Use Finset powersets/cardinality or a proved equivalent triple quotient;
prove the representative/order independence explicitly. Do not substitute
homogeneous-line determinant zero for actual finite interior concurrence:
that determinant was only a sufficient avoidance condition in fibres.

Define sign change by an actual positive delta bounded by the germ radius
and opposite signs of phi(P(t)) and phi(P(-t)) for every 0<t<delta. The
radius bound only makes evaluations meaningful; prove shrinking invariance
and the equivalence with the local source condition. No differentiability,
transversality, sign change of every coordinate, or named wall-type premise
belongs in the basic germ definition.

Full def:germ acceptance requires all these definitions and side
well-definedness, with independent source/type/body review. Partial helpers
must not increment the original PROVE count. Subsequent lem:triple-sides
requires every germ with Z_pt empty and one Z_c triple; do not add a sign-change
or transversal-parameter hypothesis. The earlier weak-locus signature
extension remains needed for flat/silent centres, which may fail G1.
