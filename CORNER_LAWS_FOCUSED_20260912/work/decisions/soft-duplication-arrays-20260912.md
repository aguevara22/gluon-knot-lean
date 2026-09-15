# Exact duplication arrays and the five-row ordinary table

Architecture proposed by /root; implementation and proofs authored by /root/review_contraction_candidates, the same currently available model. This is an untested 40-declaration candidate, not independent self-review, stronger-model statement-fidelity approval, source acceptance or a proof of recurrence satisfaction. No Lean kernel/build/audit was run. Root owns checking and review. Only new work/checks artifacts and this note were written.

The source role is the formal far/near prescriptions and ordinary-array table in SM2 lines 1223–1268. The body uses the frozen linear duplication indices and canonical NearFar types. All helper core sizes and distinguished positions are retained: there is no NeZero, n>=3, interior-position or geometric hypothesis. Actual source-size and cyclic-neighbor specialization remain later work.

## Total triple arrays

`tripleContainsBoth` spells out membership of A and B among the three actual fields. `triple_contains_both_iff` proves that this is exactly the union of middle=A, upper=B and lower=A, middle=B. Constructor cases cover the possible occurrence placements. The remaining seven placements contradict strict increase or would put a natural-number position strictly between the consecutive values s.val and s.val+1. `triple_exception_disjoint` rules out the two exceptional patterns occurring simultaneously.

For a triple not containing both occurrences, `collapseTriple` takes the three actual collapsed fields. Each strict inequality follows from the already checked collapse_lt_iff_of_lt: the only possible equality would be one of the excluded adjacent A,B pairs. No caller-supplied collapsed-triple strictness is required. `oldTriple` uses the actual increasing old embedding. It cannot contain B, and collapse_old recovers all three original fields; triple extensionality then identifies the entire collapsed triple, including proof-irrelevant bounds.

`tripleLift` is total for an arbitrary value type R. It first assigns t(collapse lower) to the upper exceptional pair, then t(collapse upper) to the lower exceptional pair, and otherwise evaluates H0 on the derived collapsed triple. All three branch equations and exact oldTriple recovery are proved. A triple containing B without A is included in the plain pullback branch; it is not dropped merely because it contains the new occurrence.

The two generic positional inequalities show collapse p<s when p<A, and s<collapse p when B<p. Applying them to the exceptional triple fields proves that the t argument differs from s. Thus a total t on Fin n may extend the source's data away from s arbitrarily at s without that extra value being read in an exceptional entry.

`coreNear` is exactly the requested rational auxiliary near array: t(lower) when middle=s, zero otherwise. Its active lower argument is strictly less than s. `parentNear` is tripleLift applied to coreNear and the same t, so the parent exceptional entries and all plain pullbacks use the source prescription. It is not claimed to be a chirotope. The definitions do not assume sign-square identities or an inverse-array solution.

## Actual interval cases and the ordinary lift

`intervalContainsBoth` is I.left<=A and B<=I.right. Its proved iff states all four closed-interval inequalities for membership of both A and B; A<B supplies the two omitted bounds. `interval_five_cases` splits these actual endpoint comparisons into precisely: no pair, duplicate singleton, starts at A with B<right, ends at B with left<A, or left<A<B<right. The singleton equality is derived from both exact endpoints through the frozen collapse-endpoint theorem.

The nonduplicate proofs for the plain, start/end and spanning cases are derived from those case hypotheses. The strict collapsed endpoint inequalities are also proved: start collapses to left=s<right, end to left<right=s, and span has left<s<right. These inequalities show that every t endpoint argument in the exceptional ordinary rows lies outside the distinguished position. They also give genuine core intervals in every nonsingleton row.

`ordinaryLift` handles duplicateInterval first, with value one, before attempting to form any collapsed interval. In its other branch the frozen collapseInterval constructor derives strict core endpoints. It then uses contains-both, left=A and right=B decisions to give the exact five rational formulas. Separate equations expose every source row. etaMinus and etaPlus are explicit independent rational parameters here; their eventual cyclic-neighbor meanings are neither assumed nor silently specialized. Likewise b0 is an arbitrary core IntervalArray, not an assumed or constructed solution of a recurrence in this body.

The prototype does not embed the scalar group because no transform identity is proved yet. The actual composition/cut-set fibers, near/far gate transport, child-product factors, scalar summation over those fibers, all ordinary-coordinate checks, one-leaf E cases and inverse uniqueness remain independent later obligations. Exact definitions and the 40-name print list were sent to root; the useful interval and collapse APIs were sent to the independent cut-set implementer to avoid name collisions.

## Exact first-draft evidence

- Body and preserved first-draft body: `8f95d9e46a3d94453dce5fc6d67ed1047498c3c8b8d13a03af6583223d3c0ece`.
- Prototype and preserved first-draft prototype: `3a8d396581d2ec1a613f9b5c5aedfe536f7ee6590b2b759b29cd26de1280aa7f`.
- Ordered two-body manifest `work/checks/SoftDuplicationArrays-body-dependencies.json`: `0c56917963ef06f0f43e85f24cbdc0f40660a763d1528b7ca6ed3a14426bcd4a`.
- Full source, passing index receipt, canonical imports, author/architecture disclosure and draft bindings `work/checks/SoftDuplicationArrays-draft-dependency-bindings.json`: `bb96c47f47a04350d636e4aaa026a1bc0f1f68eddd1f4bd15b88fbe9b05ea58d`.

The frozen index receipt's file hashes and exact full-body embedding were checked before constructing this prototype. Both complete bodies occur exactly once. This file inspection is not a Lean-pass or source-acceptance claim.
