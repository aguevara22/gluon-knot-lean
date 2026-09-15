# Visible signature completed; regular turns and rotation next

Full def:visible is independently accepted as SM.visible_signature_definition.
Review: reviews/def-visible.json, binding 32 supporting files. Semantic hash:
82d7bfbebc8f388011238a8c467b1beb783010a64602ad4a249a94f755e1fdf9.
The actual triple, faithful support-word embedding, exact labelled-component
constancy, cyclic action, and constancy up to that action on arbitrary quotient
chamber representatives are all proved. The source explicitly permits this
labelled/equivariant reading. No weak-visible-chamber result is asserted here.

The plan below is retained as history. Use decisions/regular-rotation-next.md
for the next executable branch. This accepted source row is DEFINE, so the
original 132-proof counter is unchanged by its supporting constancy lemmas.

HISTORICAL PLAN, written before implementation. Source def:visible is
reference/SM/sm-1-polygons.tex lines 258–265.

The row is the actual triple of turn tuple, crossing set and Gauss word, plus
its constancy on chambers. Constructing a triple alone does not close it.

## Geometric word transport

1. Given equality of the actual crossing predicates for P and Q, build the
   crossing equivalence that preserves the unordered edge support. The pinned
   API Equiv.subtypeEquivRight takes pointwise predicate equivalences and has
   definitionally unchanged subtype values. Extend it to the actual Visit
   sigma types, keeping the visited edge label unchanged. No bijection of
   unrelated words is an input.
2. Expose a crossing as {i,j} for any of its two distinct fibre visits. This
   follows from crossing_card_two and finite-set subset/cardinality equality.
   Identify visitParameter on i with edgeParameter P i j using the accepted
   crossingParameter_eq_edgeParameter. The latter theorem currently takes an
   explicit pair crossing, so transport the actual crossing proof carefully.
3. In a continuous family F over a preconnected space, use the accepted
   generic_family_crossing_constant to define those equivalences. Show that
   each visitKey strict comparison is preserved: different edge blocks use
   the unchanged numerical labels; within one edge use
   generic_family_crossingOrder_constant with the actual other crossing edges.
   Equal crossing partners are already included in that theorem.
4. Compare the transported old gaussList with the independently sorted target
   gaussList. Both contain every visit exactly once and their ordering agrees;
   use List.Perm.eq_of_pairwise and key injectivity. Derive the actual gaussCycle
   and gaussWord equalities by mapping this list identity, preserving repeated
   crossing letters and the empty word.

## Signature representation and topology

Choose a faithful representation that permits comparison of dependent crossing
types. One option is to map each actual Gauss letter to its unordered edge
support in Finset (ZMod n), retaining the actual crossing set as a separate
component. If using this representation, prove that the embedding loses no
information (including repeated letters and cyclic order), and every letter
belongs to the recorded crossing set. Do not silently identify arbitrary
renamings, permutations or reversal. Another option is a dependent structure
whose word alphabet is exactly its recorded crossing set.

Prove labelled chamber constancy using actual connected components, by applying
the family theorem to the connected-component subtype or a genuine path.
generic_family_chi_constant gives turn constancy and the crossing predicate
theorem gives the actual crossing set equality.

For polygons modulo cyclic relabelling, first prove the signature's actual
relabel action using turn_shift and the accepted gaussWord_shift. Then descend
through the cyclic quotient and prove constancy on its connected components.
The accepted chamber_preimage_eq_cyclic_union identifies the preimage of a
quotient chamber with labelled chambers of the actual cyclic shifts; it avoids
assuming an arbitrary path-lifting theorem. Preserve the source distinction
between equality of labelled signatures and equality up to cyclic relabelling.

## Acceptance

Bind all source clauses in one aggregate with inputs only n>=3, P and Generic P,
plus quantified genuine chamber membership where appropriate. Obtain independent
source/type/body review and a current audit before accepting def:visible. Do not
claim visible-chamber (weak-locus) constancy from generic chamber constancy alone.
This is one original DEFINE row; supporting lemmas do not increase the 132-proof
baseline. No literature interface or additional axiom is needed for this branch.
