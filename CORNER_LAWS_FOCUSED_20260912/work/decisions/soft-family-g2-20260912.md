# Soft G2 and one chamber by compact closed triples

Author: /root/review_contraction_candidates, same currently available model as root. This is an untested implementation, not independent self-review, stronger-model fidelity approval or source acceptance. No Lean kernel/build/audit was run. Root owns checking and independent review. Frozen sources, existing bodies, canonical modules and maps were not edited.

The seven declarations prove the genericity and chamber part of lem:soft-generic(i), source SM2 lines 991–1150, using a direct compactness argument rather than assuming inherited-point separation or the full crossing enumeration.

1. `g1_no_adjacent_closedTripleMeet`: with three distinct edge labels and one adjacent pair, the canonical G1 intersection theorem makes the pair's intersection its shared vertex. In either orientation that vertex cannot be an endpoint of the third edge: one endpoint equality contradicts a label inequality directly; the other cancels equal successor labels. G1 then excludes it from the third closed edge.
2. `generic_no_distinct_closedTripleMeet`: case analysis on all three remoteness relations either applies the preceding result after an explicit permutation, or applies the canonical G2 characterization for pairwise remote closed triples. This proves exclusion for all distinct parent closed triples.
3. `edgeSegment_softInsertion_parent_zero`: equality of every actual affine edgePoint at zero transfers the complete closed segment, including the return corresponding to parent j. This is not inferred from equality of endpoints alone.
4. `soft_parent_closedTriples_persist`: each distinct triple of actual corresponding labels has no closed meeting at zero by the previous two results. The canonical closedness of ClosedTripleMeet follows from compactness of the unit parameter cube and applies to arbitrary tuples, including this nongeneric zero tuple. Its open complement pulls back under continuous_softInsertion. A finite intersection over all parent triples and a metric neighborhood give one two-sided radius.
5. `softInsertion_small_Generic`: choose one common positive radius for those triple exclusions, child G1 and soft-edge avoidance. Under child G1 it suffices to exclude remote closed child triples. A remote pair containing the soft edge has neither the incoming nor the return as its other edge; the exact successor formulas and remote_endpoints prove those exclusions, so soft-edge avoidance forbids a common point. Every remaining child label is an actual corresponding parent edge. Distinct child labels force distinct chosen parent labels, and their closed meeting contradicts the finite persisted exclusion. Thus child G2 is proved, without a child Generic premise or crossing-classification dependency.
6. `softInsertion_small_G2`: exposes the derived G2 clause alone, with the same source inputs.
7. `softInsertion_one_chamber`: map the connected subtype Ioo(0,delta) continuously into the actual GenericTuple space using the proved Generic witnesses. Its connected range lies in the labelled connected component of its value at delta/2. Continuous polygonProjection gives the quotient chamber as well. The midpoint lies strictly inside the interval; no Generic point at epsilon=0 is used.

The public inputs are n>=3, arbitrary attachment j, parent Generic, and actual SoftAdmissible. The parent closed-triple persistence allows arbitrary q. The common radius is chosen before all positive parameters. The final chamber statement explicitly supplies a generic midpoint and, for every positive parameter below the radius, a generic witness and membership in both fixed actual chambers.

This route proves G1/G2 and one chamber only. It does not yet assert all crossing correspondences, uniqueness or separation of a newborn point from inherited points, inherited parameter/order convergence, or Gauss-word adjacency. The existing soft-edge contact theorem is a dependency; the new theorem does not repackage its endpoint equalities. No current inherited-crossing or classification body is imported.

The prototype has ten full bodies, each once: BoundaryTripleSupports, CanonicalTripleSigns, SoftInsertionIndices, SoftInsertionSuccessors, SoftInsertionTuple, SoftParentEdges, SoftLocalDeterminants, SoftFamilyG1, SoftEdgeAvoidance, and SoftFamilyG2. It uses the two passing ParentEdges/EdgeAvoidance receipts to order dependencies and unions their canonical imports, adding explicit GenericTopology and CyclicChambers. Dependency metadata binds exact source receipts, canonical inputs and body bytes. Exact first drafts were saved before root testing.

## Exact first-draft bindings

- work/checks/SoftFamilyG2.body.lean: 27be5e01086f99918cfa387946e4a22bf317eb427eccd54eb7fa091d9457a3f5
- work/checks/SoftFamilyG2.prototype.lean: 378b1f234a98c494c4bcc47de0acb4fa71451ba57c0d3274dc453398af0040c4
- work/checks/SoftFamilyG2-first-draft.body.lean: 27be5e01086f99918cfa387946e4a22bf317eb427eccd54eb7fa091d9457a3f5
- work/checks/SoftFamilyG2-first-draft.prototype.lean: 378b1f234a98c494c4bcc47de0acb4fa71451ba57c0d3274dc453398af0040c4
- work/checks/SoftFamilyG2-body-dependencies.json: 364f4b7df6c0aa051ac6b770a5102ed52e137d3de09a144cef2947b78fcc2d08
- work/checks/SoftFamilyG2-draft-dependency-bindings.json: dee06625a4a092eb7d555869e0d2c8c357df854bae54cc8275f541ca9adb51ae
- reference/SM/sm-2-amplitude.tex: 014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf
