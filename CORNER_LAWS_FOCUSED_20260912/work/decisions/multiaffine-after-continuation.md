# Next source obligation: the unrestricted multi-affine polynomial

Checkpoint083 proves a Lean-checked candidate for full thm:A-continuation:
SM.A_continuation gives a unique integer-valued function on every WeakTuple,
constant on actual visible connected-component chambers and equal to the
original treeCoefficient on every generic tuple, for each fixed physical root.
Its construction uses the actual relative-general-position path and E/C laws;
no path certificate or R premise remains. All24 additions are candidates,
pending stronger statement/definition-fidelity approval and controlled canonical
integration/checker acceptance. Keep accepted definitions/axioms/map,327
canonical modules, source files and all passing bodies frozen.

Next implement ALL of source lem:multiaffine, sm-2-amplitude.tex:714–797,
including its tree cut-occurrence and unary/binary clauses. Read the full
statement and proof. This is an IMPLEMENTATION PLAN, not a proof. The target
is the actual prescribed polynomial over Q in canonical unordered vertex-triple
variables, affine in EACH variable in the unrestricted polynomial ring, and
evaluating to the integer tree coefficient (cast into Q) on every G1 tuple.
Do not replace it by interpolation on realizable signs, a quotient imposing
X^2=1, an arbitrary matching polynomial, or independent variables for whole
composition weights. The same physical root must be retained throughout.

First define candidate canonical triple variables and ordered-triple signs
with a proved correspondence to the source's increasing physical labels.
The boundaryIndex map is a proved bijection for every root; use it to transport
unordered boundary triples to physical vertex triples. If a different finite
index representation is convenient, prove its bijection and exact orientation
normalization before using it as the source variables. Repeated ordered labels
must have the appropriate zero value; every actual near/far cut has distinct
labels by strict composition cuts and boundaryIndex injectivity.

Build the actual formal cut factors from the two ordered chirotope variables,
with the exact ordinary/root signs of SM.Gates and rational factor1/2. Define
formal composition weights as their finite products and the polynomial by the
actual rootedTreeRec, or its proved equivalent finite plane-tree expansion.
SM.PlaneTreeFormal.map_rootedTreeRec and treesum_trees already provide ring
evaluation and the exact finite signed tree identity. The existing
TreeWeightIndex polynomial uses independent COMPOSITION variables; it is not
itself the requested canonical-triple polynomial or a multi-affinity proof.
Derive evaluation from the nonzero gate identities on G1, explicitly respecting
integer-to-rational casts; do not transfer integer division to Q unchecked.

For one composition, define each cut's set of unordered near/far triples.
Prove injectivity of the near triples and far triples by their ordered extreme/
interior cut positions. For at least three parts, near/far equality would force
the first/last cuts to be adjacent to the same middle cut and hence two parts,
a contradiction. For two parts, prove the two ordered triples coincide in the
formal polynomial: the ordinary factor is zero and the root factor that one
variable. For one part the product is empty. SM.Gates has geometric binary
identities, but the formal-variable identities still need proofs.

Prove that cut-triple supports at different actual tree vertices cannot overlap.
SM.PlaneTreeShape, PlaneTreeWeights and PlaneTreeExpansion expose the genuine
finite recursive trees. CompositionSegments.part_bounds/part_order and
part_interior_unique provide the interval facts. Distinct children meet in at
most one boundary position, so no three-element support belongs to both. A
child interval contains exactly its two endpoints among its parent's cuts,
so no parent cut triple lies inside a child interval. Propagate these facts
down the actual tree. Ordinary nodes have at least two children and strictly
smaller child intervals (FiniteCompositions.part_leaves_lt); the unary root
may share its interval with its sole child, but has no cut factors. Retain
these explicit source clauses rather than merely assuming disjoint supports.

Then prove every formal tree weight has degree at most one in each canonical
variable: each factor is linear and different factors have disjoint variable
supports. Handle the ordinary binary zero weight and unary root cases. Finite
signed summation preserves the bound. An induction on the same actual tree
or recursion is acceptable if it also proves the stated nonrepetition clauses;
it must not replace the tree with a new representation lacking equivalence.
Use precise Mathlib polynomial degree/support facts after inspecting the pinned
local code. The source result is complete only after both the unrestricted
degree bound and exact G1 evaluation are proved and independently reviewed.

Do not evaluate gates at silent zeros: continuation was just constructed from
generic values, and the following source line-gap/polyform results are separate
obligations needed to compare polynomial evaluation there. After multi-affinity,
read pf:line-gap and its subsequent polynomial-form theorem in full and continue
the dependency chain toward the actual corner laws and soft theorem.

Use small prototypes for independent combinatorial/polynomial helpers; append
only exact frozen bodies when assembling. No new axioms, sorry/native_decide,
silent premise strengthening or source repairs. Preserve exact failures before
repair and freeze passing bodies. Root owns one Lean kernel/build/audit at a
time; reviewers none. Same-model nonauthor review remains distinct from the
stronger fidelity approval. Record candidates outside the canonical map.

Goal remains active. Progress: source19/132 (14.39%), original checklist38/191
(19.90%), expanded39/192 (20.31%), final corner targets0/8. Start one ten-minute
watcher on resumption, retain the hourly app automation, checkpoint each work
unit, and stop the exact watcher on exit. No author question is needed.
