# Filtering the actual rotation quotient

Author: /root/review_contraction_candidates, same currently available model as root. This is an untested additive implementation, not independent self-review, stronger fidelity approval or source acceptance. No Lean kernel/build/audit was run. Root owns testing and independent review. Existing canonical and frozen candidate files were not edited.

The pinned Mathlib Cycle module has map but no filter operation, and its List.Rotate module has no IsRotated.filter lemma. The new body adds nine declarations without assuming rotation compatibility.

`List.IsRotated.filter` uses the actual bounded rotation witness. If a representative splits as a prefix followed by a suffix, the rotated list is the suffix followed by the prefix. Filtering distributes over append. Thus the two filtered lists differ only by exchanging their filtered prefix and suffix, which is exactly the proved isRotated_append relation. This handles empty prefixes/suffixes, an empty result, repeated entries and every rotation amount.

`Cycle.filter (p : alpha -> Bool)` is Quotient.map' of List.filter using that theorem. Therefore it is defined on the actual quotient of lists by rotation, not on arbitrary representatives or a multiset approximation. `filter_coe` is definitional and exposes the exact list filter. The remaining interfaces prove filtering nil, membership, repeated filtering, identity when every occurring entry is kept, and preservation of Nodup.

`Cycle.filter_map` states that filtering the mapped cycle by p equals mapping the original cycle filtered by p composed with f. It follows by quotient induction from the literal List.filter_map equality and requires no injectivity. In particular f may be Sigma.fst, sending two visits to the same crossing letter. This supplies the required bridge between removing both newborn visits and removing the newborn crossing's two occurrences in a cyclic word. Predicates are Boolean, matching the underlying List.filter; crossing predicates can be expressed by decide.

Only Mathlib.Data.List.Cycle and Mathlib.Data.List.Nodup are imported. The body has no soft-geometry dependency and asserts no crossing count, Gauss identity or adjacency theorem. It provides the operation needed for the source lem:soft-generic(iv) deletion statement; the actual filtered-cycle identity and identification of the removed entries remain separate assembly proofs.

Exact initial body and prototype copies were saved before root testing. The prototype embeds the one new body once and prints all nine declarations. Dependency metadata binds the pinned Cycle/Rotate/Nodup sources and toolchain.

## Draft hashes

- work/checks/CycleFiltering.body.lean: bce25edf0380d786621b8b074deb8df65b4c4b4ff46b3ba395ddf937d935700d
- work/checks/CycleFiltering.prototype.lean: 93dc708cee82c3887314ab3aa457bebe9e8c85e2011ca2a1eb19656f1d0a2389
- work/checks/CycleFiltering-first-draft.body.lean: bce25edf0380d786621b8b074deb8df65b4c4b4ff46b3ba395ddf937d935700d
- work/checks/CycleFiltering-first-draft.prototype.lean: 93dc708cee82c3887314ab3aa457bebe9e8c85e2011ca2a1eb19656f1d0a2389
- work/checks/CycleFiltering-body-dependencies.json: 9e243092a4f39aa2ff0695821668f0bd00be70b44d4a85fb1a9581eb4c06e6ee
- work/checks/CycleFiltering-draft-dependency-bindings.json: c320145856d5e3af20396ad6782e71fe84ed63c761b6ed534ace3dcfeeafb203
