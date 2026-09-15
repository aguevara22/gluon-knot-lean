# Carrier cycle splitting inventory — 2026-09-12

Read-only implementation research by `/root/spanning_gates`. No Lean kernel was run and no proof/source file was changed. Source acceptance increment: 0; stronger statement fidelity approval: false; integration approval: false. Current recorded accepted source progress remains 19/132 (14.39%). This inventory identifies a proof route, not a checked theorem or a discharge of its generic permutation hypotheses.

The pinned library provides the orbit/list tools needed for a direct proof of the source's split-list calculation. The local two-slot splitting identity and the actual independent-support induction still require proof. Use successor orbits including fixed points: neither nontrivial cycle factors nor the library's empty list for a fixed point represents every carrier.

The pin is Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`, Lean `v4.34.0-rc2`, from `work/lean/lake-manifest.json` and `work/lean/lean-toolchain`. Below, `M/` denotes `work/lean/.lake/packages/mathlib/Mathlib/`.

The authoritative argument is `reference/SM/sm-3-statesum.tex`: smoothing and incoming ownership at lines 14–39; `lem:carriers` at 55 onward; actual successor construction and splitting induction at 97–145. It swaps outgoing slots, keeps selected endpoint identities as incoming owners, preserves inherited cyclic order, and proves that each remaining selected pair stays together because it does not interlace the processed pair. These are separate obligations, not consequences of swap commutativity alone.

Exact pinned APIs inspected:

| Location | API and usable content |
|---|---|
| `M/GroupTheory/Perm/Cycle/Basic.lean:53,77,82` | `Equiv.Perm.SameCycle f x y := ∃ i : ℤ, (f ^ i) x = y`; `SameCycle.equivalence`; `SameCycle.setoid`. These include singleton orbits. |
| Same file:106,114,119,170 | `SameCycle.eq_of_left` rules out a fixed starting point when distinct points are in one orbit; `sameCycle_apply_left/right` give orbit stability; `sameCycle_subtypePerm` identifies the restricted and ambient relations. |
| `M/GroupTheory/Perm/Cycle/Concrete.lean:202,224,229,240,273,292,338` | `Equiv.Perm.toList`; `toList_getElem_zero`; `mem_toList_iff : y ∈ p.toList x ↔ p.SameCycle x y ∧ x ∈ p.support`; `nodup_toList`; `next_toList_eq_apply`; `SameCycle.toList_isRotated`; `formPerm_toList : (f.toList x).formPerm = f.cycleOf x`. Distinct same-orbit endpoints make the old orbit nontrivial, so this list covers that old orbit. |
| `M/GroupTheory/Perm/Cycle/Factors.lean:44,78,82` | `cycleOf_apply` equals `f y` on the selected orbit and `y` elsewhere; `SameCycle.cycleOf_apply`; `cycleOf_apply_of_not_sameCycle`. These isolate the changed old cycle while retaining other cycles. |
| `M/GroupTheory/Perm/List.lean:104,127,131,147,163,180` | `List.formPerm_apply_of_notMem`, `formPerm_mem_iff_mem`, `formPerm_cons_concat_apply_last`, `formPerm_apply_head`, `formPerm_apply_lt_getElem`, and `formPerm_apply_getElem`. These give unchanged interior arrows, wraparound arrows, and behavior outside each list. |
| Same file:227,236,254; `Concrete.lean:119` | `List.formPerm_rotate`, `formPerm_eq_of_isRotated`, `formPerm_pow_apply_getElem`, and `formPerm_apply_mem_eq_next` transport a chosen list start and connect list order with successor iteration. |
| `M/GroupTheory/Perm/Cycle/Basic.lean:831` | `List.Nodup.isCycleOn_formPerm (h : l.Nodup) : l.formPerm.IsCycleOn {a | a ∈ l}`. Crucially, no length-at-least-two premise. |
| Same file:659,672,718,798; `M/GroupTheory/Perm/Basic.lean:64` | `IsCycleOn` is invariant bijective membership plus mutual `SameCycle`; `isCycleOn_singleton`; `IsCycleOn.apply_mem_iff`; `IsCycleOn.range_zpow`; `Set.BijOn.perm_zpow`. Invariant disjoint nonempty blocks yield distinct orbits, including singleton blocks. |

The next generic proof can start with finite `α`, `f : Equiv.Perm α`, `a ≠ b`, and `f.SameCycle a b`. First derive `f a ≠ a` using `SameCycle.eq_of_left`. Use the concrete orbit list, whose first entry is `a`, and split at its unique `b` to obtain a duplicate-free list `a :: (A ++ b :: B)`. The new local identity to prove by the displayed successor APIs is:

```lean
(a :: (A ++ b :: B)).formPerm * Equiv.swap a b =
  (a :: B).formPerm * (b :: A).formPerm
```

Equation (1). This is a proposed proof obligation, not an existing lemma. Its pointwise cases are `a`, `b`, entries of `A`, entries of `B`, and entries outside the old list. At `a`, right multiplication takes the old outgoing arrow at `b`; at `b`, it takes the old outgoing arrow at `a`. All other arrows are unchanged. Empty `A` or `B` produces a singleton child and must remain allowed.

The old orbit therefore partitions into the disjoint nonempty node sets of `a :: B` and `b :: A`. Prove the new permutation agrees with each child's `formPerm` on its set. Transfer `Nodup.isCycleOn_formPerm` to these two invariant sets; `IsCycleOn.range_zpow` then identifies them as exactly the two new orbits. In particular, `a` and `b` cannot be in one new orbit: their sets are disjoint and invariant under every integer power by `Set.BijOn.perm_zpow`. Outside the old orbit, prove all old orbits are unchanged. This yields orbit refinement, endpoint separation and the one-to-two replacement. A quotient-cardinality proof must count all `SameCycle` classes; `cycleFactorsFinset` omits fixed points. No exact quotient-cardinality increment theorem was identified in the inspected permutation files.

For the actual construction, let `rho := markSuccessor hn hP` and `f := smoothingSuccessor hn hP T`. `work/checks/CarrierSmoothing.body.lean` defines the latter as `(selectedMarkPerm T).trans rho`, hence `rho` after the selected permutation. For a new crossing `c ∉ T`, choose one actual visit `v` of `c` and put `a := Sum.inr v`, `b := Sum.inr (visitTwin v)`. The following identity must be proved from the constructed singleton switch and the disjoint-union API:

```lean
smoothingSuccessor hn hP (T ∪ {c}) = f * Equiv.swap a b
```

Equation (2). `Equiv.trans` applies its left argument first, whereas permutation multiplication applies its right argument first. Left multiplication by `swap a b` would exchange incoming targets instead and would not express the source's displayed outgoing-arrow rule. `CarrierVisitTwin.body.lean` supplies actual twin distinctness, exhaustion and involution; no arbitrary pairing is needed. `CarrierSmoothing.body.lean` already exposes `selectedMarkPerm_union_of_disjoint`, `smoothingSuccessor_union_of_disjoint`, `owner_eq_iff`, `Component`, and the empty-support single-component result. Their candidate receipt status must be checked before implementation depends on them.

The actual independence and inherited-order link remains substantive:

1. From `SM.mem_independentSupports` (`work/lean/SM/InterlaceSupports.lean:32`) and `SimpleGraph.isIndepSet_iff` (`M/Combinatorics/SimpleGraph/Clique.lean:860`), extract noninterlacement of distinct selected crossings. `SM.interlaces_iff_unique` (`work/lean/SM/InterlaceCount.lean:20`), actual two-visit exhaustion, and `SM.crossingVisitBetween_complement` (`work/lean/SM/Interlacement.lean:35`) give that both visits of another selected crossing occupy the same original open arc between the new pair. This same-arc consequence still needs a proved lemma.
2. Maintain an induction invariant for every processed support: each current orbit has a cyclic list inherited from the actual original `markList`, and every remaining selected pair lies in one current orbit. The initial orbit is supplied by `markSuccessor_sameCycle`; `markList_nodup`, `markList_sorted`, `markKey_injective` and `markPosition_visit` tie its order to actual traversal positions. The original order is `traversalBetween`, defined by three strict key-order cases in `SM/Traversal.lean:73`.
3. Formally connect an open sublist between two current endpoints with the corresponding original `traversalBetween` arc restricted to that orbit. Being an arbitrary enumeration of the same orbit is insufficient. A suitable representation is a rotation of the original list filtered to the orbit; after splitting, both child lists remain such cyclic subsequences. This is a proposed representation whose equivalence and preservation need proof.
4. Apply Equation (1) only after the actual same-current-orbit invariant has been established. Noninterlacement plus inherited order then puts each remaining selected pair in one child. Other current orbits are unchanged. Orbit refinement ensures previously separated selected endpoints remain separate. The count increases once per selected crossing, giving the source's count after the quotient-cardinality step.

This directly advances clause (i). It does not yet establish carrier polygon geometry, regularity, all-visits noncrossing ownership, rotation, named-record or coefficient transport, or either corner soft/wall theorem. It assumes no residual polygon `G1` and discharges no such geometric premise.

Search scope: enumerated all files under `M/GroupTheory/Perm`, read `Cycle/Basic`, `Cycle/Concrete`, `Cycle/Factors` and `Perm/List`, and searched `swap`, `SameCycle`, `cycleOf`, `IsCycleOn`, `split`, `merge`, and the combined patterns `sameCycle.*swap|swap.*sameCycle|split.*cycle|cycle.*split|swap.*formPerm|formPerm.*swap` under `M/GroupTheory` and `M/Data/List`. Also inspected canonical `SM/InterlaceSupports`, `Interlacement`, `InterlaceCount`, `Traversal`, `TraversalArcs`, and current CarrierMarks/VisitTwin/Successor/Smoothing bodies. No general two-slot splitting theorem surfaced in this bounded search; different names or other locations are not ruled out. The nearby `IsCycle.swap_mul` (`Cycle/Basic.lean:425`) removes one adjacent point from a nontrivial cycle under additional premises; it is not the arbitrary two-endpoint, two-orbit theorem needed here.
