# Next gap: the complete named-wall definition

After the full deletion/halves and children acceptance, finish original
def:walls (reference/SM/sm-1-polygons.tex:710–750) before the much larger
transport-polynomials/relative-general-position chain. Do not redo the accepted
wall-sides, cusp-sides or children source lemmas. All current 203 pre-children
SM files and the newly reviewed children files must retain their reviewed bytes.

## Scope and existing evidence

NamedWallPredicates already defines the exact F/V/T/E/C, BigonAt and SlidingAt
predicates. CuspDefinition defines exact K/CuspAt. These are independently
reviewed dependencies, but the wholedef:walls is still pending: its mutual
exclusivity, full named side/empty conventions, centre-determination and cyclic
compatibility have not all been assembled/proved. Implement new modules; do not
change an accepted dependency merely to update an old introductory comment.

1. Use the six printed kinds F,K,V,T,E,C, with a separately proved bigon/sliding
partition within V. Represent source simplicity by existence of one actual
printed named-wall predicate. Do not define an unproved property to be true by
construction or assert that every nongeneric germ is simple.
2. Form transparent central conditions for those kinds by keeping the actual
zero/concurrence sets and geometry and omitting only the SignChanges clauses.
Prove each actual named predicate implies its central condition. Prove central
conditions of different kinds are incompatible. This supports the source's
centre-determination claim between already simple germs without falsely claiming
that the centre determines whether an arbitrary germ is tangent/transverse.
3. Reuse turnSupport_injective for n>=4 and contactSupport_successive /
contactSupport_vertex_edge to prove uniqueness of the contact base and marked
vertex from the same support. Singleton equalities identify supports. The
existing contactSupport_ne_turnSupport and noConsecutive_ne_turnSupport separate
F/K from V/E and C; a contact support itself has a consecutive pair, separating
V/E from C. T has empty point-zero set, unlike all other kinds.
4. Separate F from K using their actual between/outside conditions (or proved
Regular versus cusp_not_regular). V and E have the same unique marked contact
but respectively inside/outside the actual closed base segment. Non-K centre
regularity is already proved by the accepted geometry. Keep unordered T/C
supports insensitive to permutations, and retain every source size bound.
5. Prove centre-determination of the six kinds from central incompatibility,
and the V bigon/sliding classification from the actual central neighbour chi
equality. Then actual named-wall mutual exclusivity follows without using
unproved general position or classifying arbitrary singularities.

## Named sides and empty convention

6. At F, use GermTurnSigns.side_turn_constant and turn_signChanges_opposite,
plus actual Generic nonzero turns, to define/derive the unique right(-1) and
left(+1) side. Both may be evaluated at independent SideParameters. Do not
assume a coorientation from the author.
7. At V, define the contact sign as actual chi on the negative side. Prove
independence of its chosen positive-distance parameter and nonzero sign using
generic_family_chi_constant and the source's distinct contact indices. Keep
bigon/sliding central equality, not a guessed local drawing.
8. At K, reuse the full accepted cusp theorem: unique central case, exact
newborn support, unique loop Bool, opposite no-loop side. Define empty using
the actual cyclic successor adjacency of the two newborn visits. Prove this
condition independent of side parameter; do not merely choose sideBase and
call it well-defined. generic_family_gaussList/gaussCycle in GaussFamily.lean
provide full actual list/cycle transport, using the support/edge-preserving
visitTransport equivalence from CrossingTransport. Prove next/adjacency commutes
with that equivalence and identify the transported first/last newborn visits.
The already reviewed GaussVisitsAdjacent retains wraparound and two-visit cases.
9. Prove cyclic parent relabelling for all actual predicates and marked labels,
including singleton support images, CuspCase/selected pair/side/empty, F sides,
V central subtype/contact sign and the unordered T parameter-difference sign
changes. Reuse GermRelabel, ZeroTripleRelabel, edge/chi/turn shift and actual
GaussRelabel. SignChanges is the real local product condition, so sign reversal
from permutations is handled algebraically, not discarded.
10. Assemble the entire definition and obtain independent statement/body review,
then a fresh whole audit before accepting the original definition row. If a
representation uses a labelled model, supply the proved cyclic equivariance;
never replace source geometry by arbitrary supplied combinatorial records.

This work uses no literature interfaces and does not close any of the main
state-sum wall laws or the soft theorem. The unrestricted original lem:shift
zero-turn issue remains separately recorded and does not block these tasks.

## Completion — checkpoint047

All ten steps are complete in SM.NamedWallsDefinition. Independent full review
reviews/def-walls.json accepted the source definition and final audit047 passed.
Original proof count remains13/132; checklist is28/191. Continue with
decisions/transport-polynomials-after-walls.md; do not repeat this plan.
