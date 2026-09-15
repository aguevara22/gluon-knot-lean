# Shift/reversal source omission — independently confirmed

Source: reference/SM/sm-1-polygons.tex, lem:shift, lines 484–509.
The edge/chirotope and individual-turn formulas apply to arbitrary labelled
tuples. Genericity is preserved, and actual homeomorphisms should carry
connected-component chambers onto chambers. Rotation identities apply on the
actual regular locus. These are useful independent obligations.

The printed aggregate left-turn formula has no explicit nonzero-turn premise.
The surrounding section does not impose Generic globally; the regular locus
explicitly permits positive collinearity and zero turns. The candidate regular
four-tuple with natural labels 0,1,2,3 is ((0,0),(1,0),(2,0),(0,1)). Its turns
are (1,0,1,1), so the reversed left count is 0 while 4 minus its left count is
1. This exact counterexample is now kernel checked and independently reproduced
in repairs/ShiftZeroTurn.lean. The final successful log lists only standard
axioms. See reviews/lem-shift-scope.md and repairs/index.json.

Independent review confirmed the omission and absence of a standing premise. Do not map a Generic-restricted theorem as
the unrestricted source row or claim the original row accepted. Formalize an
exact counterexample if the omission is confirmed. The faithful general count
is left(reverse P) = number of right turns of P; consequently the source
formula holds when all turns are nonzero. It is enough for the observed
consumers (generic C-reversal and generic star anchors), but this does not
silently repair the original source statement. Preserve source and baseline.

Next: prove actual reversed affine edges, closed/interior set equalities,
G1/G2 invariance, exact crossing support bijection, generic homeomorphisms and
component image equalities. Prove the count under an explicit nonzero-turn
hypothesis and keep any repair separated from original acceptance. Continue
independent main-target prerequisites without asking the author.


The true reversal geometry, Generic preservation, actual crossing-set image,
actual generic/quotient homeomorphisms and complete component image equalities
now compile in GenericReversal, ReversalCrossings and ReversalChambers.
TurnCountReversal proves the unrestricted right-turn count and the corrected
n-left formula under explicit nonzero turns, including a proved Generic
corollary. ShiftReversal assembles the proposed repair without mapping it to
the original source row. All are included in passed audits025/026; independent
repair review is complete in reviews/lem-shift-repair.md. The original baseline remains 132 proof obligations.
