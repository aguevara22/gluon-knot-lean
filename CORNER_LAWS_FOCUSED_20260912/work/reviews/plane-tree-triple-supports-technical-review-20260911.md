# Actual tree cut-support nonrepetition: technical review

Root did not author PlaneTreeTripleSupports; review_contraction_candidates is
the author, including the dependent-pattern repair. This is same-model
nonauthor technical review, not stronger fidelity approval. No source acceptance.

Compared the full source lem:multiaffine and the actual canonical OpenPlaneTree,
RootedPlaneTree, parts/part, part_bounds and previous composition-support body.
No defect found in the scoped 23 declarations.

CutOccurrence is recursively the sum of actual top cut indices and a dependent
pair of child index and child occurrence. Leaves are empty. It therefore retains
the actual node address and cut, with no quotient by equal leaf intervals.
Finite/Fintype are derived structurally, including arbitrarily deep trees.

Support bounds propagate the actual child interval endpoints through part_bounds.
The full support union is over all actual occurrences. The parent-vs-child
lemma combines the child's bound with the proved impossibility of containing a
parent cut triple. Sibling union disjointness derives equal child indices from
containment of an increasing triple in both intervals and contradicts inequality.

Pairwise disjointness handles four top/descendant cases. Top/top uses actual
cut-factor disjointness, top/descendant uses consecutive-cut geometry, same-child
uses structural induction with equality of dependent occurrences justified by
substitution, and distinct-child uses interval separation. Nonrepetition is
exactly disjointness contradicted by a shared triple. Binary near/far coincidence
remains inside one cut factor. Rooted proofs add the same cases with no arity
restriction. The unary lemma eliminates all root cuts by the empty Fin(parts-1)
type and puts every occurrence in its actual child.

These prove boundary-position nonrepetition. Physical canonical variable
transport is supplied separately by boundaryTripleData_injective; polynomial
support and degree bounds and the explicit internal-interval exception are
separate work. These helpers do not yet prove all of lem:multiaffine.

First65349 failed to elaborate the dependent node pattern in cutTripleSupport;
the exact first body/prototype/log were preserved. Second46937 passed after
binding the node and children before matching its occurrence. No declaration
type changed. All 23 printed traces use only the three allowed foundations.

work/checks/CompositionTripleSupports.body.lean SHA-256: c6600e67a028ccffb28c0aae1d02e782b689f24e823ddd3a49b297e0cb069cff
work/checks/PlaneTreeTripleSupports.body.lean SHA-256: d21ef16f9f91c4ec13e1642badf233620c8f761e6b5c398f22b7aa7cea224b82
work/checks/PlaneTreeTripleSupports.prototype.lean SHA-256: 2dad6e95e6ab270fb7927a97e736d68d41b3cd672d5b782adfc5935cda0ba90d
work/checks/PlaneTreeTripleSupports-second-kernel.log SHA-256: 02c33a583a774300a083f4e85701a2d32429ff096efc641bbfadd4ded653db30
