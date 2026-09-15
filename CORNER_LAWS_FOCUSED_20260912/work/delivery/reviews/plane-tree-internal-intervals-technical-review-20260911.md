# Actual internal-node intervals: technical review

Root did not author PlaneTreeInternalIntervals; author is
review_contraction_candidates. This is same-model nonauthor technical evidence,
not stronger fidelity approval. No source claim is accepted.

Compared all19 declarations against full lem:multiaffine714–797 and canonical
OpenPlaneTree, RootedPlaneTree, composition parts, containing_part_unique,
part_leaves_lt, UnaryComposition and actual BoundaryInterval semantics.
No defect found in this scoped review.

InternalOccurrence includes every ordinary node, including binary zero-weight
nodes, and RootedPlaneTree.InternalOccurrence adds the distinguished root even
when unary. Structural IsTopInternal and IsImmediateChild inspect constructors;
neither is defined by the target equality of intervals. Equality is proved later.

Endpoint bounds propagate to every descendant. Leaf-count monotonicity follows
from the actual endpoint inequalities; strictness then uses each ordinary node's
constructor arity>=2 and the canonical strict child-size theorem. Ordinary
internalInterval injectivity exhausts top/top, top/descendant, and both subtree
cases. Equal sibling descendant intervals would fit in two child intervals,
forcing the child indices equal by containing_part_unique; induction then fixes
the exact dependent node occurrence. Binary ordinary nodes are retained.

For root-child equality, parts cannot be>=2 because the child's positive leaf
interval is then strictly smaller. parts_pos forces parts=1. The complete unary
composition is the single composition, whose child interval is the parent.
The remaining equality characterizes the immediate child's actual top. The
converse is also proved. Descendants under distinct root children have injective
intervals by the same argument. Consequently distinct rooted internal nodes
with equal intervals are precisely allowed only by the unary root and its
immediate internal child, in either order. No unique root/generic geometry or
cut-carrying assumption excludes the empty-product case.

unary_cut_product proves the empty product is1 for every CommMonoid assignment,
not just evaluated gate values. It uses the empty actual Fin(parts-1) domain.
Root first17495 exited0; all19 traces use only the three allowed foundations.
Passing body/prototype/log/receipt are frozen. Stronger fidelity remains pending.

work/checks/PlaneTreeInternalIntervals.body.lean SHA-256: d517acbe05348e7f6c80d244e0150e32209e0ee7e9f2326c4799e2beff8d6b63
work/checks/PlaneTreeInternalIntervals.prototype.lean SHA-256: baae45a6e557de3b83fface096e2be5998c0db91a2290609f7010248a645a172
work/checks/PlaneTreeInternalIntervals-first-kernel.log SHA-256: 5c5ac64be7f1600ba9113eacc07d8690481fd44b69625feffc98d4e1ee8dd5ba
