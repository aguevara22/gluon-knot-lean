# Actual newborn visits and the empty short arc

Author: /root/review_contraction_candidates, the same currently available model as root. This is an untested implementation draft, not independent self-review, stronger-model statement-fidelity approval, or source acceptance. No Lean kernel/build/audit was run. Root owns testing and independent review. All source, canonical modules and previous passing bodies remain unchanged.

The source role is the actual newborn visits and empty short arc in lem:soft-generic(iv), SM2 lines 1034–1042 and 1140–1148. The thirteen-declaration body uses only frozen dependencies. Adjacency through the generic empty-arc converse will be a separate additive wrapper, once that converse has passing evidence.

## Actual objects and geometric values

`softNewbornIncomingVisit` and `softNewbornReturnVisit` have exactly `softNewbornCrossing hclass hloop` as their crossing component. Their member edges are the actual enlarged incoming label `softOldIndex j (j-1)` and return label `softNewIndex j`. Both membership proofs use the actual two-element newborn support. Their crossing and edge identities are definitional; their distinctness follows from the proved old-index/new-index separation.

`softNewbornVisits_exhaust` proves that every actual child visit with this crossing component is one of these two visits. It transports the visit's existing edge membership to the exact newborn pair, splits the two membership possibilities, and uses canonical visit extensionality. There is no freely chosen visit labelling or assumption that other member edges do not exist.

`softNewbornVisits_parameters` applies the frozen transverse crossing-data uniqueness theorem to this actual crossing object. The incoming and return visit parameters therefore equal the existing Cramer parameters, with the return direction measured from the inserted vertex toward the next old vertex. `softNewbornVisits_interior` supplies both strict parameter bounds from actual child G1.

`softNewbornVisits_physical_path` exports exact successor-edge identities: incoming edge plus one is the soft edge at old j; soft edge plus one is the return edge. Their vertices evaluate to P j and P j + epsilon*q. Thus the edge path and its physical endpoints are explicit, including j=0. This body does not separately assert `traversalBetween` for the two zero-parameter vertex positions. If the final source packaging uses that exact predicate for passage through both vertices, that additional predicate-level consequence remains to be proved; the endpoint identities are not silently presented as such a theorem.

## From finite parameter windows to an actual empty arc

`softNewbornVisits_inherited_bounds` takes the explicit frozen pairwise window proposition as a helper input. For each parent visit, `crossing_pair_of_mem` derives the other member edge and the exact parent support. `softInheritedVisit_parameter` identifies the actual transported parameter with the pair's edgeParameter. The incoming or return label hypothesis then selects the correct window, while the newborn parameter theorem converts its bound to the actual visitParameter. This gives strict inequalities for all inherited visits on the two incident parent edges.

`softNewbornVisits_no_between` splits an arbitrary child visit by whether its crossing is the actual newborn. In that branch, the two-visit exhaustion above reduces to one of the arc endpoints, where the strict cyclic-order predicate is false. Otherwise the frozen exact inherited-visit range gives an actual parent visit whose image is the child visit. The checked `soft_parent_traversal_arc_empty` applies to its three actual traversal positions. The mapped edge identities supply its edge hypotheses; the two strict window inequalities supply the weaker inequalities that exclude intervening points on the incoming or return edge. All other parent edges are excluded by the exact cyclic predecessor/successor arithmetic already proved in ParentArc. Its zero-label branch covers the cyclic seam.

`soft_newborn_small_empty_arc` discharges every helper premise on one common positive interval. It takes the minimum of the checked transport radius, finite visit-window radius and newborn transversality radius. The first gives actual child Generic, complete crossing persistence and complete support classification; the latter two give the determinant and both parameter windows. The loop-sector proof is quantified after each epsilon and its derived data. The conclusion supplies inherited bounds and excludes every actual child visit from the oriented incoming-to-return arc. No child Generic at epsilon=0, new geometric assumption, gap oracle, extra size bound, or nonempty parent-crossing assumption occurs.

## Exact first-draft evidence

- Body and first-draft body SHA256: `d2941ad22159da33739481a53b856d794a45fc62a9c9a0bd8c5026fc01659d7e`.
- Prototype and first-draft prototype SHA256: `67b77770e53a830db98dc4a83f0fe0b864f2380f9b958ff08cc9041644bb7bc1`.
- Ordered 20-body manifest `work/checks/SoftNewbornVisits-body-dependencies.json`: `b2e7207203b220488184291aa78d7338b050edcca9ad93201aa5f42a4fbf27c5`.
- Full draft/source/receipt bindings `work/checks/SoftNewbornVisits-draft-dependency-bindings.json`: `190ecc5b6b293ab85eb3bbf8193966492da80df800aacdfdb9fd92b8080a43d4`.

The prototype unions the actual ordered full-body embeddings in the passing SoftCrossingTransport, SoftNewbornVisitWindows and SoftParentArc prototypes, deduplicates by path, and appends this new body. All source-receipt file hashes and each full-body single embedding were checked by ordinary file inspection only. The prototype prints axioms for exactly the thirteen new declarations. This is not a Lean pass claim.
