# Actual soft crossing and visit transport

Author: /root/review_contraction_candidates, same currently available model as root. This is an untested 27-declaration implementation draft, not an independent self-review, stronger-model fidelity approval or source acceptance. No Lean kernel/build/audit was run. Root owns checking and independent review. Only new work/checks artifacts and this note were written; frozen bodies, source and canonical modules remain unchanged.

The source role is the inherited crossing/visit correspondence and exact newborn complement in lem:soft-generic(iii–iv), within SM2 lines 991–1150. This body does not assert Gauss-list or cyclic-order identities.

## Derived interval data

`SoftCrossingPersistence P j q epsilon` is explicitly every actual parent pair crossing implying that its two mapped edge labels form an actual child crossing. `SoftCrossingClassificationAt` spells out the full frozen support iff: inherited pair, or the incoming/return support in the exact loop sector. Neither predicate contains an assumed map or bijection.

`soft_small_crossing_transport_data` proves both predicates and actual child Generic on one positive interval from n>=3, parent Generic, arbitrary j and actual SoftAdmissible. It intersects the remote-pair, support-classification and Generic radii. Every parent crossing supplies its remoteness through the canonical crossing predicate, so the remote-pair iff gives the required forward persistence. The radius is chosen before epsilon; no additional persistence/classification/Generic oracle remains for the actual family. The zero-parameter tuple is not assumed Generic.

## Crossing maps and range

`softInheritedCrossing hp c` has precisely `c.val.image (softParentEdge j)` as its support. A parent crossing's actual pair representation and hp prove that this image lies in Crossing. Injectivity is Finset.image_injective for the proved injective parent-edge map, followed by subtype extensionality.

The inherited/newborn supports cannot coincide by the frozen classification lemma: their injective preimages would make the adjacent parent incoming/outgoing pair an actual parent crossing. `softInheritedCrossing_range_iff` proves that a child crossing has a parent preimage exactly when its support differs from the newborn pair. The reverse implication applies the exact classification to the child crossing and reconstructs the parent crossing from the inherited branch; the other branch contradicts the excluded support.

`softInheritedCrossingEquiv` is an equivalence onto the actual subtype of non-newborn-support child crossings. `softCrossingEquivNonloop` is a full equivalence when the loop conjunction is false. `softNewbornCrossing hclass hloop` is an actual child Crossing with the incoming/return support, derived from classification. `softInheritedCrossing_range_loop` states the complement using inequality to this actual Crossing object, not only a support label. These constructions require no chosen external bijection.

## Visit maps and parameters

`softInheritedVisit hp v` maps the actual crossing and maps the member edge by softParentEdge. Finset.mem_image supplies the actual membership witness. The crossing and edge formulas are definitional. Visit injectivity combines crossing-map injectivity and parent-edge injectivity, then the canonical visit extensionality lemma. `softInheritedVisit_pairing` preserves exactly equality of crossing components, hence the two-visit pairing.

`softInheritedVisit_range_crossing_iff` proves that a child visit is inherited exactly when its crossing is in the crossing map's range. For the nontrivial direction, its member edge lies in the image support; choose its parent member edge from Finset.mem_image and use visit extensionality. The crossing range theorem then gives the exact inherited-visit subtype, the non-loop full visit equivalence and the loop complement of all visits whose crossing is the actual newborn. No visit is excluded merely by its edge label.

`softInheritedVisit_parameter` identifies the transported visit's actual canonical visitParameter with the child edgeParameter on the two mapped parent labels, for any presentation of that parent's two-element support. It obtains the actual pair crossing, identifies the visit with pairVisit and applies the canonical parameter equality under child G1. `softInheritedVisit_parameter_exists` derives a suitable other label for every visit from crossing_pair_of_mem. Child G1 is supplied by the actual interval data above. Parameters are not claimed numerically unchanged under insertion; this interface connects to the frozen convergence and same-edge order theorems.

The empty parent crossing set, every root position and cyclic seam, parent n=3 and both sectors remain included. The body proves support/membership/parameter transport and full image exhaustion. Numerical parent-edge order, sorted Gauss-list equality, cyclic adjacency and Gauss-word deletion remain separate root work.

The prototype unions the frozen Classification and G2 dependencies in their actual prototype order and adds SM.PairVisits. Fifteen complete bodies occur once each. The ordered list and draft bindings name every source receipt, body and canonical visit interface. Exact first drafts were saved before root testing.

## Exact first-draft bindings

- work/checks/SoftCrossingTransport.body.lean: f307ede65952da40f90c7edae9f7e1abccb65f41275b380151fb8df8377e094f
- work/checks/SoftCrossingTransport.prototype.lean: ddba294f49d8d71aa6ab9ea619c817a7745be54641a206edbc52786eb70cd6c0
- work/checks/SoftCrossingTransport-first-draft.body.lean: f307ede65952da40f90c7edae9f7e1abccb65f41275b380151fb8df8377e094f
- work/checks/SoftCrossingTransport-first-draft.prototype.lean: ddba294f49d8d71aa6ab9ea619c817a7745be54641a206edbc52786eb70cd6c0
- work/checks/SoftCrossingTransport-body-dependencies.json: 350f3d9b295a182e5e7fa99d53a26d2d1a7ac1d02b3bcf87b514b28aba9710c8
- work/checks/SoftCrossingTransport-draft-dependency-bindings.json: 2889e0953f8f116e8ddf7319a50339c8e3b156672c68f0f282e6704e1730da34
- reference/SM/sm-2-amplitude.tex: 014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf
