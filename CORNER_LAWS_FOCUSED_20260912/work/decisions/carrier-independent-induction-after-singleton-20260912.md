# Independent carrier induction after the singleton case — 2026-09-12

Read-only next-step note by `/root/spanning_gates`. No kernel, proof edit, source edit, source acceptance, stronger fidelity approval or integration approval. This describes new obligations, not proofs already discharged. Candidate dependencies must have passing receipts before assembly uses them.

Fix the actual generic polygon, its complete `Mark P := ZMod n ⊕ Visit P`, and a final independent support `S`. Induct over processed `T ⊆ S`, with `fT := smoothingSuccessor hn hP T`. The original successor and the current successor must remain distinct objects. `markSuccessor_splitList` describes the complete original circle; after processing crossings, it does not describe an arbitrary current orbit.

The current exact interfaces are:

| Candidate body | Relevant existing API |
|---|---|
| `CarrierSameArc.body.lean:131` | `independent_twin_one_open_arc hn hP hS v w hvS hwS hvw` puts both actual visits of another selected crossing in one **original** open arc. It does not assert they lie in the same current orbit. `not_interlaces_iff_twin_same_arc` provides the equivalent Boolean arc-status form. |
| `CarrierCycleList.body.lean:9,28,41` | `markSuccessor_eq_formPerm`; `markList_rotate_split` gives a literal rotated original list `a :: (A0 ++ b :: B0)`; `markSuccessor_splitList` additionally gives Nodup, original permutation equality and completeness on every mark. |
| `CarrierSplitList.body.lean:83,139,148,158,170,182` | `splitList_identity`; both child `IsCycleOn` statements; both exact `SameCycle` membership iff statements; `splitList_not_sameCycle`. The two children are `a :: B` and `b :: A`, including singleton children. |
| `CarrierSingleSwitch.body.lean:41,68` | `smoothingSuccessor_insert hn hP T v hv` is exactly `fT * swap (Sum.inr v) (Sum.inr (visitTwin v))`; `smoothingSuccessor_insert_other` preserves every other outgoing slot. |
| `CarrierSingleSupport.body.lean:9,28,39,65` | `smoothingSuccessor_singleton_splitList`, `owner_singleton_ne`, `owner_singleton_exhaust`, `component_card_singleton`. These handle the first actual split, not later current-cycle representations. |
| `CarrierOrbitRefinement.body.lean:41,60,69,76,83,93` | `smoothingSuccessor_insert_sameCycle_refines`, `owner_insert_ne_of_ne`, `componentForgetSwitch`, its owner formula and surjectivity, and the weak count inequality. Every actual insert theorem here retains the explicit premise `hc : fT.SameCycle (Sum.inr v) (Sum.inr (visitTwin v))`. |

Use the following proposed actual component-order representation. For `q : Component hn hP T`, filter `markCycle hn hP` by the Boolean predicate `decide (owner hn hP T m = q)`. Call this filtered cycle `CT q` provisionally. Its nodes include ordinary vertices and all crossing visits assigned to `q`, including selected visits under incoming ownership. It has no dependence on an arbitrary enumeration or supplied pairing.

The located filtering API is the **candidate** `work/checks/CycleFiltering.body.lean`, not a canonical `work/lean/SM/CycleFiltering.lean` file: `List.IsRotated.filter`, `Cycle.filter`, `filter_coe`, `mem_filter`, `filter_filter`, `filter_eq_self`, and `Cycle.Nodup.filter`. These supply well-defined filtering modulo rotation, exact membership and Nodup. `owner_surjective` supplies a mark in each component, hence nonemptiness. None of these APIs proves that the filtered list's cyclic successor equals the current smoothed successor.

The induction must maintain two simultaneous invariants:

1. For every current component `q` and every mark `m` owned by `q`, `fT m` is exactly the next mark in `CT q`. This is an equality on that component; the whole ambient permutation is not the filtered list permutation, since other components also move. This is the required inherited cyclic-order statement.
2. For every remaining crossing `c ∈ S \ T`, its actual twin visits lie in one `fT` orbit. This supplies `hc` when `c` is processed. The proof cannot replace this with their membership in the original circle, which is true for all marks and says nothing about current ownership.

At `T = ∅`, filtering retains the complete circle because all original owners coincide. `smoothingSuccessor_empty`, `markSuccessor_sameCycle` and the construction of `nextMark` prove both invariants. This also retains original vertices when the crossing set is empty.

For an insert step, choose the actual visits `a := Sum.inr v`, `b := Sum.inr (visitTwin v)` of `c ∈ S \ T`. The second invariant gives `q0 := owner T a = owner T b`. Rotate the **original** list using `markList_rotate_split`, then filter it by `owner T = q0`. Since `a` and `b` survive, the filtered representative is literally:

```lean
a :: (A0.filter keepQ0 ++ b :: B0.filter keepQ0)
```

Equation (1). Thus `A := A0.filter keepQ0` and `B := B0.filter keepQ0` are current open arcs with their original inherited order. This construction avoids substituting the full original split list for a current cycle. The first invariant identifies this filtered representative's successor with `fT` on `q0`.

Apply `splitList_identity` to the filtered representative. A still-needed local transport proof must show that the actual inserted successor agrees on `q0` with its split-list permutation, and that the two list-orbit membership characterizations transfer to the ambient successor. Both directions require orbit invariance; pointwise agreement alone without closure is insufficient. The children are `a :: B` and `b :: A`. Components other than `q0` retain their entire old successor orbits because neither switched mark is in them and all their outgoing arrows are unchanged.

For the inherited-order invariant after insertion, prove the actual new owner predicates on `q0` equal membership in these two child lists. `Cycle.filter_filter` then reduces each child's original-circle filter to the corresponding current-cycle filter; the source split lists are cyclic subsequences of the old representative. Outside `q0`, the old and new ownership blocks coincide and their filtered cycles retain the same next relation. Do not identify quotient types or quotient representatives by unproved definitional equality.

For the remaining-pair invariant, take another `d ∈ S \ (insert c T)`. If its current owner differs from `q0`, its two visits stay together by unchanged-orbit transport. If its owner is `q0`, `independent_twin_one_open_arc` places both visits in one original open arc of `a,b`. The missing original-slice/order lemma below converts that fact to both lying in `A0` or both in `B0`; current ownership puts both in the corresponding filtered list `A` or `B`. Therefore they enter the same child. Previously split selected endpoints remain apart by `owner_insert_ne_of_ne`, now with its `hc` premise supplied by the maintained invariant.

The exact plus-one count should use the constructed `F := componentForgetSwitch hn hP T v hv hc`, not just its surjectivity. Prove its fibers as follows:

- Over `q0`, the fiber consists exactly of the two distinct new owners of `a` and `b`. `componentForgetSwitch_owner` gives membership. Local split separation gives distinctness. For exhaustion, represent a new component by a mark using `owner_surjective`; its image being `q0` puts that mark in the complete current filtered list, and the child membership partition gives one of the two endpoint owners. This proves a fiber equivalence with `Fin 2` or an equivalent two-element cardinal statement.
- Over every `q ≠ q0`, surjectivity gives a preimage, and unchanged-old-orbit transport makes any two preimages equal. This gives a unique fiber element. Refinement alone only says new orbits cannot merge; it does not prove these other fibers are singletons.

Use pinned `Equiv.sigmaFiberEquiv F` (`Mathlib/Logic/Equiv/Sum.lean:236`) and `Fintype.card_sigma` (`Mathlib/Data/Fintype/BigOperators.lean:158`) to sum those exact fiber sizes. Every old component contributes one, and `q0` contributes one additional element. Then `Finset.card_insert_of_notMem` and the empty-support count close the count induction. Singleton mark orbits are counted throughout; `cycleFactorsFinset` is unsuitable for this count because it omits fixed points.

The next first executable packet should be **CarrierMarkedArcLists**, about 6–10 bounded lemmas. Its substantive target is: for an actual rotated complete-list presentation `markList.rotate k = a :: (A0 ++ b :: B0)`, prove `m ∈ A0` iff `traversalBetween (markPosition a) (markPosition m) (markPosition b)`, and the reverse-arc analogue for `B0`. Endpoints are excluded on both sides. Then prove the filtered forms by conjunction with the actual owner predicate, and the literal filter identity in Equation (1) when `a,b` have owner `q0`. Use `markKey_injective`, `markList_sorted`, and the three strict key-order cases in canonical `SM.traversalBetween` (`work/lean/SM/Traversal.lean:73`). Cover wraparound explicitly. Canonical `SM.sorted_next_no_cyclic_between` (`work/lean/SM/SortedCyclicGap.lean:10`) verifies a consecutive gap has no intervening retained node, but does not by itself characterize every open slice of a rotated list; that stronger characterization is the new proof.

After that packet, implement the actual filtered component cycle and the simultaneous induction, using a bounded local orbit-split transport/fiber packet as needed. This order directly connects existing SameArc8 to actual current-cycle membership. It leaves carrier geometry, regularity, all-visits noncrossing ownership, rotations, named records, coefficient transport, and the corner soft/wall laws open; no residual polygon G1 premise is introduced.
