# Next source candidate: vertex-edge tree law thm:A-S7

Checkpoint079 completes a checked candidate for source thm:A-S4. Its final
cusp_tree_law derives the unique central case and a single integer rotation
jump before all independent side parameters and all physical roots. This is
still a dependency toward the main corner theorem; stronger fidelity approval
and canonical integration remain pending. Keep accepted definitions, axiom
policy, map, canonical modules, sources and all passing candidate bodies frozen.

Next read source sm-2-amplitude.tex:520–590, its induced-root definition:380–393,
and the actual VertexEdgeAt / child predicates in source context. Implement
thm:A-S7 for both bigon and sliding cases without a neighboring-side restriction.
The following is an IMPLEMENTATION PLAN, not a checked proof or new axiom.

Existing canonical APIs inspected: ContactHalfSizes gives contactDistance,
firstHalfSize, secondHalfSize and their source-domain bounds. ContactHalfIndices,
ContactHalfTuples and ContactHalfSupport give the actual full vertex tuples,
range/index facts and edge preservation. firstHalf has the source closing root
-1, directed a to M; secondHalf has the source opening root0, directed M to a+1.
Their inherited physical roots use firstHalfIndex away from -1 and
secondHalfEdgeIndex away from0. Read exact types before constructing the map.

First prove an exhaustive disjoint root partition: base root g=a; roots on the
original M-to-a arc; roots on the original a+1-to-M arc. The inherited cases
must include the edges incident to each named endpoint. Build a concrete typed
half-root pair: (-1,0) at the base, (inherited first index,0) in the first arc,
(-1,inherited second index) in the second arc. Prove its physical-edge meaning,
not only a modular root-number formula. Discharge every size/domain clause from
the exact printed assumptions; do not silently impose a larger parent arity.

For each cut prove the precise boundary positions and critical triple, gap
leaf counts, and proper/full span. Derive affine coordinates A=0,B=1,X=r with
0<r<1 from the actual center contact interior. The reverse far sign is minus
chi(A,B,X) in all three cyclic orders. Reuse the integer single-triple response.

At g=a the cut order is B,X,A. Both gaps are nonleaf, both epsilon signs positive:
the U product vanishes and the V product is the product of the two actual half
coefficients at roots0 and-1. Prove the complete restricted-word/half tuple
identities and transport G1, arity and coefficients. Reorder the scalar product
by commutativity while preserving the names of the halves.

On the first inherited arc the cut order is A,B,X, left gap singleton and right
gap the nontrivial second-half word, epsilon(+,-). Prove properness and the full
contracted tuple identity with firstHalf at the inherited physical root. On the
second arc the cut order is X,A,B, left gap the nontrivial first-half word and
right singleton, epsilon(-,+). Prove the analogous full secondHalf identity.
The earlier generic arity-transport and contraction-position helpers can be
reused; one-vertex deletion formulas must not be applied to these longer arcs.

Only after all actual tuple/coefficients and three cases are proved, assemble
the product law with the source sign s=chi(A,B,X) on its named P-minus side.
Check the source named-side convention against the canonical contactSign API;
do not identify either named side with a time sign without a proof. The generic
same-side chirotope helper can remove a local-radius restriction if needed.
Obtain nonauthor same-model technical review; do not count it as stronger
fidelity approval. Keep source thm:A-S7 and all final corner targets pending
until their own proof, fidelity and checker obligations are fulfilled.

Root owns one Lean kernel/build/audit at a time. Start one ten-minute watcher on
resumption and retain the existing hourly automation. Preserve every failed
attempt before repairs; bind successful bodies/prototypes/logs in receipts.
Accepted source proofs remain19/132 (14.39%); expanded checklist39/192 (20.31%);
final targets0/8. No author question is required.
