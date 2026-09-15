# Next proof: inherited order after one actual insertion

Authored by `/root/spanning_children`; bounded independent analysis, 2026-09-12.
No candidate/source edits, kernels, builds, audits or acceptance. This is a proposed
proof sequence, not a checked theorem. The inspected `CarrierInsertOrbits` is the
root's three-declaration draft; its receipt is not established by this analysis.
The reviewer authored the earlier filtered-cycle, inherited-order and unaffected
block packets; this contribution overlap is explicit.

## Inputs and exact target

Use `hn`, `hP : Generic P`, processed support `T`,
`hI : InheritsMarkOrder hn hP T`, an actual visit `v`, freshness
`hv : v.1 ∉ T`, and the explicit current-owner equality `hc` of `v` and its twin.
Let `a = Sum.inr v`, `b = Sum.inr (visitTwin v)`, `T' = insert v.1 T`,
and `q = owner hn hP T a`. The proposed final theorem is
`inheritsMarkOrder_insert hn hP T hI v hv hc : InheritsMarkOrder hn hP T'`.
It needs no independence premise; the later simultaneous induction must derive
`hc` from independence and its unprocessed-pair invariant.

Obtain one common witness `k,A,B` from
`smoothingSuccessor_insert_child_data`. Keep its literal full-original rotation,
and set `AL = A.filter old` and `BL = B.filter old`, where
`old m = decide (owner hn hP T m = q)`. The two child lists are
`CL = a :: BL` and `CR = b :: AL`.

Crucially, `a :: (A ++ b :: B)` represents the full original circle;
`L = a :: (AL ++ b :: BL)` represents only the affected old component.
There is no assertion that this old component is the full circle.

## Derive the two affected cycle equalities

1. Reconstruct the old inherited representative with exactly these witnesses:
   `componentCycle_eq_filtered_splitList hn hP T q k a b A B hrot rfl hc.symm`.
   It gives `componentCycle hn hP T q = (L : Cycle (Mark P))`.
   Apply `componentCycle_list_nodup` to this equality to obtain `L.Nodup`.
   The insertion child-data theorem already supplies both child Nodup proofs,
   disjointness, global new-owner membership equivalences and child actions.

2. Let `qL = owner hn hP T' a` and `qR = owner hn hP T' b`.
   Define `newL m = decide (owner hn hP T' m = qL)` and analogously `newR`.
   Prove **globally**, for every actual mark `m`, that either new predicate
   implies `old m`. For the left predicate, its supplied owner equivalence
   puts `m` in `a :: BL`. The head has owner `q` by definition; membership
   in `BL` gives old-owner equality by `List.mem_filter`. For the right
   predicate, membership is in `b :: AL`; the head uses `hc.symm` and the
   tail again uses `List.mem_filter`. Thus no outside old component can enter
   either new predicate. This derivation does not require orbit refinement
   as an extra premise.

3. Prove the filter absorption on the **full original markCycle**. For each
   `new` among `newL,newR`, the preceding implication proves pointwise
   `(new m && old m) = new m`. A direct case split on the actual new-owner
   equality, using the derived old-owner equality in the true branch,
   avoids propositional automation issues. `Cycle.filter_filter` then gives:

   `(markCycle.filter old).filter new = markCycle.filter new`.  (1)

   The right side is the actual new `componentCycle` by its definition;
   the first filter on the left is the actual old `componentCycle`.
   Only after proving (1), replace the old cycle by `(L : Cycle _)` from step 1.
   This is the needed justification for working inside the old component.

4. The global owner equivalences identify `newL` with
   `fun m => decide (m ∈ CL)` and `newR` with `fun m => decide (m ∈ CR)`.
   Use `funext` and `decide_eq_decide.mpr` on those equivalences, then
   `Cycle.filter_coe`. Apply the already passing generic helpers at **AL,BL**:
   `filter_splitList_left a b AL BL hN` retains `a :: BL`;
   `filter_splitList_right a b AL BL hN` retains `AL ++ [b]`.
   The latter represents `b :: AL` by
   `Cycle.coe_eq_coe.mpr (List.isRotated_concat b AL)`.
   This establishes the actual equalities:

   `componentCycle hn hP T' qL = (CL : Cycle _)` and
   `componentCycle hn hP T' qR = (CR : Cycle _)`.  (2)

   Keep `List.filter_congr` plus `decide_eq_decide.mpr Iff.rfl` between
   concrete and generic membership-filter instances before applying
   `congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))`.
   The earlier singleton proof required this explicit instance transport.

A bounded next packet can package steps 1–4 as an existential strengthening of
`smoothingSuccessor_insert_child_data`, retaining the same `k,A,B`, both exact
new cycle equalities and both child action clauses. Do not choose fresh,
unrelated split-list witnesses halfway through the proof.

## Prove the inherited-order insertion theorem

Use `inheritsMarkOrder_iff_formPerm`. Given an arbitrary new component `r`,
choose `m` with `owner hn hP T' m = r` using `owner_surjective` and replace `r`
by that actual owner. Set `q0 = owner hn hP T m` and split on `q0 = q`.

* If `q0 ≠ q`, use `componentCycle_insert_unaffected` with the actual
  representative `m`. The new inherited cycle equals the old cycle at `q0`.
  A tested mark in that cycle therefore has old owner `q0`, by
  `mem_componentCycle`. Old `hI` gives its old filtered-cycle formPerm action;
  `smoothingSuccessor_insert_eqOn_owner` says the new action there is the
  old action. These equalities give the required new formPerm action.

* If `q0 = q`, `componentCycle_list_mem_iff` applied to step 1 puts `m` in
  `L`. Split its membership into `m=a`, `m∈AL`, `m=b`, or `m∈BL`.
  The first and last cases give membership in `CL`; the middle two give
  membership in `CR`. The child-data global owner equivalences identify
  `r` with `qL` or `qR`. Transport the applicable equality (2); membership
  of any tested mark becomes membership in that child list. The supplied
  child action clause then proves the formPerm requirement. No component
  count or unproved global component classification is needed here.

For formPerm transport, reuse the successful Nodup-subtype method from
`CarrierInheritedOrder` / `componentCycle_list_eqOn`: form equal elements of
`{s : Cycle (Mark P) // s.Nodup}`, apply `congrArg` to
`fun s => s.val.formPerm s.property`, explicitly `change` away subtype
projections, and then use `Cycle.formPerm_coe`. Direct rewriting of a cycle
under its dependent Nodup proof failed in the preserved singleton attempts.
All steps allow empty `AL` or `BL`, and hence singleton child cycles.

## Remaining simultaneous induction

Fix an actual independent ambient support `S`, and maintain for each processed
`T ⊆ S` both `InheritsMarkOrder T` and equality of the two current owners for
every crossing still in `S \ T`. The empty case follows from the checked
original one-orbit result. For insertion of `v`, the second invariant supplies
`hc`; the proposed insertion theorem supplies inherited order.

For another remaining pair `w`, its old common owner either differs from `q`
or equals `q`. In the first case `owner_insert_iff_of_unaffected` preserves
its shared new owner. In the second, use
`independent_twin_same_filtered_slice` with the ambient `hS`, the actual common
old-owner equalities and the same `hrot`. Both marks lie in `AL` or both in
`BL`; the two global child-owner equivalences then give a common new owner.
Distinctness from `v.1` follows because `w` remains outside the inserted support.
This is where the checked physical marked-arc facts discharge the co-location
step; they do not by themselves identify current components.

The exact plus-one component count, geometric carrier regularity and the final
corner soft/wall theorems remain separate obligations. This analysis grants no
source acceptance, stronger fidelity approval or canonical integration.

## Inspection snapshot

| Inspected body | SHA256 |
|---|---|
| `CarrierInsertOrbits` | `aae25eb4b54e369cd659180523607046436c5c7dfbab96c0942bee26adddc782` |
| `CarrierCurrentCycle` | `c87fd76d5d9962354b4bfe9e045548874fad917be37cdc1022ee152e263edd53` |
| `CarrierFilteredCycles` | `17e091e45f8844dc366f67f985691accf2678d3a529692278113c3099ff2649e` |
| `CarrierMarkedArcLists` | `62ac3c5aacf04887eab399f8fa06c7120730623776711c43e87316bf4c0bc270` |
| `CarrierInheritedOrder` | `b2436d72abd3f351fc8c48615fd8af9e672a4b1d5c2bf7d896b076b40aa947b8` |
| `CarrierUnchangedComponent` | `7301b73e3e90cce8a902632193a5eb25687a9f72800f7305771a404b8ae5fc66` |
