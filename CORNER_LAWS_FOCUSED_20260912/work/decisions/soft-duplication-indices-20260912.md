# Linear occurrence duplication indices

Author: /root/review_contraction_candidates, same currently available model as root. This is an untested 32-declaration implementation draft, not independent self-review, stronger-model statement-fidelity approval, or source acceptance. No Lean kernel/build/audit was run. Root owns checking. Only new work/checks artifacts and this note were written; all passing bodies, source and canonical modules remain unchanged.

The source role is the formal duplication setup and interval endpoint exception in SM2 lines 1224–1270, within the A-soft proof at 1217–1402. This model is the linear ordered boundary word. It does not identify the linear embedding with a cyclic soft edge or assert a root-cut word identity.

For arbitrary s : Fin n, namespace SM.SoftDuplication defines A=s.castSucc, B=s.succ, old=(B s).succAbove, and collapse=s.predAbove. The definitions use canonical Fin operations, and the standalone prototype imports only canonical SM.RootBoundary and Mathlib Fin modules. There is no NeZero, n>=3, interior-s, or endpoint exclusion premise. The source core sizes and both endpoint duplications are therefore included; when n=0 there is simply no s : Fin n.

The exact old numeric formula keeps k.val when k<=s and uses k.val+1 otherwise. The collapse formula keeps p.val when p.val<=s.val and subtracts one otherwise. These follow from the canonical branch formulas for succAbove/predAbove, not from an assumed inverse. old_self identifies the retained occurrence with A. The canonical strict monotonicity theorem gives order preservation and injectivity, and succAbove_ne proves that B is omitted.

collapse_old is proved in the two old-position branches: below or at s, predAbove cancels castSucc; above s, it cancels succ. This supplies the explicit left inverse. collapse_A and collapse_B both equal s. The canonical predAbove monotonicity supplies collapse_monotone. Away from B, the canonical succ_succAbove_predAbove theorem recovers the actual original child position. child_exhaust splits off B and otherwise constructs the preimage as collapse p, proving exhaustion without a choice oracle.

The fiber over s is exactly {A,B}. A point equal to B gives the second alternative. Every other point is recovered from its collapse by old_collapse_of_ne_B, and collapse p=s then identifies it with old s s=A. For k different from s, a preimage cannot be B because collapse B=s; the same reconstruction identifies it uniquely with old s k. Both pointwise iff statements and exact Set preimage equalities are provided.

For p<q, collapse_eq_iff_of_lt proves that equal collapsed values force p=A and q=B. After taking Fin.val, the two piecewise numeric formulas have four branch combinations. If both points lie on the same side of s, equality contradicts their strict order. In the only possible cross-side case, p<=s<q and p=q-1 force p=s and q=s+1. The reverse implication is collapse_A=collapse_B. Combining this exact equality exception with monotonicity proves that collapse is strictly increasing on every other increasing pair.

The optional interval interface is included. duplicateInterval has endpoints A,B and exactly one leaf. For any actual BoundaryInterval I, equality of its collapsed endpoints is equivalent to I=duplicateInterval. The forward proof applies the ordered-pair exception and then identifies the interval from both exact endpoints; proof irrelevance handles its increasing proof. Every nonsingleton-duplicate interval has strictly increasing collapsed endpoints, so collapseInterval constructs a genuine core BoundaryInterval from I and only its inequality to duplicateInterval. Callers do not supply an extra distinct-endpoint witness.

The body does not prove the five-case interval partition, composition/cut-set fiber bijections, neighboring near-gate transport, or transform/product identities. Those are the next source obligations. The exact API was sent directly to /root/review_mark_transport, which is independently implementing concrete cut-set fibers. No result in this body assumes those later identities.

## Initial bindings

- Body and exact first-draft body: `0232499719a463712b836a8fe74f0d988b54df6e379bb30a9f39a938548f3703`.
- Prototype and exact first-draft prototype: `ec4b590de4b43278ce99a1cc5169d6b357ad1656b98e3535653b0675276ed150`.
- Single-body dependency manifest `work/checks/SoftDuplicationIndices-body-dependencies.json`: `892df3fd96afb73fe38f769401066d92e667498c3ba6972a4ba1d64817823f1a`.
- Exact declaration print list and source/canonical/draft hashes `work/checks/SoftDuplicationIndices-draft-dependency-bindings.json`: `462ef2adb38801637f6d395baa51db951a573971100a0f604ab20b2b888c9775`.

The prototype contains this complete body exactly once and prints all 32 new declarations. These hashes and source checks are file inspection, not a kernel-pass or source-acceptance claim.
