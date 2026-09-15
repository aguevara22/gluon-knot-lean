# Interlacement completed — historical plan

Full def:interlace is independently accepted as SM.interlacement_definition.
Review: reviews/def-interlace.json. Its semantic hash is
08dd9e9d028d04b3703385337c6084f2cc6c27074348ae2242f9d48408d97a47.
The full construction proves the alternating/count equivalence, arbitrary
endpoint choice, symmetry, actual graph and full Ind/N/U definitions, and
cyclic transport. N/U accept arbitrary supports, and Ind includes empty.
No original PROVE row is added by these supporting lemmas.

The plan below is retained as history. def:visible is now also accepted; see
decisions/visible-signature-next.md for its completion record. The next
executable branch is decisions/regular-rotation-next.md.

HISTORICAL PLAN, written before implementation. Source:
reference/SM/sm-1-polygons.tex lines 247–265. The actual Gauss construction is
implemented through SM.GaussDefinition; consult its current map/review status.

## Interlacement

Use actual `Visit P` values and `visitPosition hn hP.1`, not an arbitrary word
or graph. A source-faithful existence definition is: distinct crossings x,y
have visits v0,v1 of x and w0,w1 of y, each pair distinct, with
traversalBetween(v0,w0,v1) and traversalBetween(v1,w1,v0). These are the four
alternating visits in oriented cyclic order. Include their crossing projections.

Prove the four-point cyclic-rotation lemma for traversalBetween using its
explicit real inequalities. It turns witnesses v0,w0,v1,w1 into
w0,v1,w1,v0 and gives symmetry of interlacement. Self-adjacency is excluded by
the distinct-crossing clause. Prove representative independence by transporting
all four visits through visitShiftEquiv, using its crossing projection and the
already proved arbitrary-point traversalBetween_shift equivalence.

The source also says “exactly one visit of y” lies between x's two visits.
Prove equivalence with that clause, including independence of which x visit is
called first. For two distinct x-fibre visits, the fibre is exhausted by those
two because visits_per_crossing is exactly 2. Likewise for y. The two open
cyclic arcs are complementary on y's visits because generic visit positions
are injective and x != y. This gives the one-of-two count in both directions.
Do not replace this equivalence by the definition of an arbitrary input graph.

Then construct `SimpleGraph (Crossing P)` with that actual adjacency. Define
all independent finite supports, including the empty support, N(S) as crossings
interlacing an element of S, and U(S) as the complement of S union N(S) in the
actual finite crossing domain. Expose membership equivalences and relabelling
compatibility before independent review of the full definition.

Pinned APIs inspected: SimpleGraph.IsIndepSet (Clique.lean:857) is exactly
Set.Pairwise non-adjacency; Finset.card_eq_two gives a two-element presentation;
Finset.card_pair and finite-cardinality subset equality can prove exhaustion.
The current source crossingSet and crossingFintype are equivalent finite domains.

## Visible signature

The signature consists of the actual turn tuple, actual crossing set and Gauss
word. Its statement also asserts chamber constancy. Use the accepted chamber
path theorem and an explicit bijection identifying Crossing P with Crossing Q
when their actual crossing predicates agree. The Gauss lists should coincide
under that bijection because all visits occur once and every geometric ordering
comparison is preserved. Finite sorted-list uniqueness then gives the word
identity. Preserve the source cyclic quotient and prove the needed transport;
do not compare dependent words by pretending their crossing types are identical.

No new literature axiom is needed for these constructions. Helpers are not
additional original proof claims. Keep all eight main roots and the full
132-proof/191-checklist baseline unchanged.
