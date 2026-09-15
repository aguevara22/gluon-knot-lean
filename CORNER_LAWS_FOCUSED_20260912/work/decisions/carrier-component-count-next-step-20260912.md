# Actual quotient component count: next proof packet

Read-only inventory by `/root/spanning_gates`, 2026-09-12, checkpoint102. No Lean kernel, verifier or audit was run, and no proof candidate was edited. Source acceptance increment0; stronger fidelity and canonical integration remain unapproved. Paths below are relative to the focused root. This is an implementation route, not a checked proof.

The source target is `reference/SM/sm-3-statesum.tex:54–92`, `lem:carriers(i)`: an independent support has exactly its cardinality plus one carriers, with inherited cyclic order and selected visits on different carriers. The proposed packet counts the already constructed actual successor-orbit quotient `Component`; geometric carrier realization and the other source clauses remain separate.

`CarrierOrbitRefinement` and `CarrierInsertOrbits` are passing frozen packets. The sealed `CarrierPendingPairs` receipt was observed with exit0 during this inventory. `CarrierInheritedInsert` and `CarrierIndependentOrder` had bodies but no result receipt when read; their displayed APIs below are draft dependencies, not asserted checked results.

## Existing exact inputs

- `work/checks/CarrierSmoothing.body.lean:97–135`: `Component hn hP T` is the actual quotient of `Mark P` by successor `SameCycle`; `owner hn hP T`, `owner_eq_iff`, `owner_surjective`, and `componentFintype` supply its quotient map, equality criterion, representatives, and finiteness. `component_card_empty` at line154 proves the empty count is one.
- `work/checks/CarrierOrbitRefinement.body.lean:70–100`: `componentForgetSwitch hn hP T v hv hcOrbit`, its definitional `componentForgetSwitch_owner`, and `componentForgetSwitch_surjective` are proved from actual successor refinement. The existing count theorem is only `component_card_le_insert`.
- `work/checks/CarrierInsertOrbits.body.lean:10`: `smoothingSuccessor_insert_child_data hn hP T hI v hv hc` derives an original rotated complete mark list, two owner-filtered child lists, their Nodup and disjointness, exact child-owner membership iff for every ambient mark, and child successor actions. At line60, `owner_insert_iff_of_unaffected hn hP T v hv hc q hq m hm z` proves exact equality of the new owner of `z` with that of representative `m` iff its old owner is `q`.
- `work/checks/CarrierMarks.body.lean`, `mem_markList`, and pinned `Mathlib/Data/List/Rotate.lean:113`, `List.mem_rotate`, give completeness of that same original rotation. `CarrierCurrentCycle.body.lean:53`, `componentCycle_current_split_data`, is an alternative source of complete owner-filtered current membership, but it is unnecessary to invoke a second independently chosen rotation.
- Draft `work/checks/CarrierIndependentOrder.body.lean:9`: `independent_partial_invariants hn hP hS T hTS` returns `InheritsMarkOrder hn hP T ∧ PendingPairsTogether hn hP S T`. Its `independent_remaining_pair_owners` at line40 directly discharges the fresh pair owner equality. These results must pass before use in an assembled count consumer.

## Smallest direct fiber interfaces

Work with the existing assumptions `hn : 3 ≤ n`, `hP : Generic P`, `T : Finset (Crossing P)`, `hI : InheritsMarkOrder hn hP T`, `v : Visit P`, `hv : v.1 ∉ T`, and
`hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v))`.
Set `a := Sum.inr v`, `b := Sum.inr (visitTwin v)`, `q0 := owner hn hP T a`, `qL := owner hn hP (insert v.1 T) a`, `qR := owner hn hP (insert v.1 T) b`.
Use `hcOrbit := (owner_eq_iff hn hP T a b).mp hc` and the actual map `F := componentForgetSwitch hn hP T v hv hcOrbit`. No new pairing or partition is an input.

A first bounded packet needs only the following three substantive results. Names are proposed, not present checked declarations:

1. `componentForgetSwitch_fiber_affected hn hP T hI v hv hc`:
   `qL ≠ qR ∧ (Finset.univ.filter (fun r => F r = q0)) = {qL, qR}`.
2. `componentForgetSwitch_fiber_unaffected hn hP T v hv hc q hq m hm`, with `hq : q ≠ q0` and `hm : owner hn hP T m = q`:
   `(Finset.univ.filter (fun r => F r = q)) = {owner hn hP (insert v.1 T) m}`.
   This theorem needs no inherited-order hypothesis. Its representative is explicit; callers obtain it from `owner_surjective`, so no arbitrary correspondence is assumed.
3. `component_card_insert hn hP T hI v hv hc`:
   `Fintype.card (Component hn hP (insert v.1 T)) = Fintype.card (Component hn hP T) + 1`.

The first result can be split into endpoint distinctness and affected-fiber exhaustion if useful for proof size. There is no need to introduce a new fiber structure or a generic supplied finite partition.

To prove the affected fiber, obtain the *one* `smoothingSuccessor_insert_child_data` witness, with original arcs `A,B` and filtered arcs `AL,BL`. Distinctness follows because an equality `qL=qR` would place `b` in `a::BL` by the left child iff, while `b` is the head of `b::AL`, contradicting child disjointness. This proof does not demand either arc be nonempty.

For exhaustion, take an arbitrary new quotient component `r` and choose an actual mark `m` using `owner_surjective` at the new support. The equation `F r=q0` becomes `owner hn hP T m=q0` by `componentForgetSwitch_owner`. Completeness of `markList.rotate k` and its returned split equality put `m` at `a`, in `A`, at `b`, or in `B`. In either interior case, the old-owner equation adds precisely the filter predicate, giving membership in `AL` or `BL`. Thus `m` belongs to one of `a::BL` or `b::AL`; the corresponding exact child-owner iff gives `r=qL` or `r=qR`. Conversely `F qL=q0` is definitional, and `F qR=q0` follows from `hc.symm`. Finset extensionality turns this iff into the literal pair fiber.

For an unaffected fiber, choose the supplied old representative `m`. For any new representative `z`, `F (owner_new z)=q` is exactly `owner_old z=q`. Apply `owner_insert_iff_of_unaffected` to identify its new owner with `owner_new m`; the converse follows from `hm`. This proves the singleton filter equality without assuming that the old component is the whole original circle.

## Pinned cardinality APIs and exact arithmetic

All cited Mathlib files are under `work/lean/.lake/packages/mathlib/Mathlib/` at pinned revision `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

- `Algebra/BigOperators/Group/Finset/Basic.lean:993`, `Finset.card_eq_sum_card_fiberwise [DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t)`: the cardinality of `s` equals the sum over `t` of `s.filter (fun a => f a = b)` cardinalities. Instantiate `s` and `t` with the actual new and old quotient `univ`; the MapsTo proof is simply membership in old `univ`.
- `Data/Finset/Card.lean:797`, `Finset.card_eq_two`, converts the affected literal fiber and proved endpoint distinctness to cardinality two. `Finset.card_singleton` handles every unaffected fiber. `Finset.card_univ` identifies the two total finite-set cardinalities with `Fintype.card`.
- `Algebra/BigOperators/Group/Finset/Basic.lean:749` generates `Finset.add_sum_erase (s) (f) (h : q0 ∈ s)`. Its orientation is `f q0 + sum over s.erase q0 = sum over s`. At line968, `Finset.sum_const_nat` evaluates the remaining fiber sum, since each remaining fiber has cardinality one.
- `Data/Finset/Card.lean:156`, `Finset.card_erase_add_one`, gives `((univ.erase q0).card) + 1 = univ.card`. It avoids truncated natural subtraction. Consequently the fiber sum is two plus the erased cardinality; regrouping and this equality give the old cardinality plus one. No nonzero divisor or positive-length child assumption appears.

If a later consumer specifically needs subtype fiber counts, `Data/Fintype/Card.lean:395`, `Fintype.card_subtype`, converts them to these exact finite filters. An alternative total-space count uses `Logic/Equiv/Sum.lean:236`, `Equiv.sigmaFiberEquiv F`, `Fintype.card_congr`, and `Data/Fintype/BigOperators.lean:158`, `Fintype.card_sigma`; the direct Finset route has fewer type-level obligations here.

## From one step to independent support count

After the independent invariant packet passes, add `component_card_independent_partial hn hP hS T hTS` with conclusion `Fintype.card (Component hn hP T) = T.card + 1`; then specialize `T=S` for `component_card_independent hn hP hS`.

Induct on the actual Finset `T` with fixed independent `S`, reverting `hTS : T ⊆ S`. At an insertion of crossing `c`, obtain the old subset inclusion and `c∈S`. `SM.crossing_visits_exist c` (`work/lean/SM/CrossingPair.lean:9`) supplies a real visit `v := ⟨c,i⟩`. The draft independent partial invariants give the old inherited order and the pending owner equality for this `v`; apply the checked proposed one-step count. The induction hypothesis replaces the old component cardinality, and `Finset.card_insert_of_notMem` (`Data/Finset/Card.lean:104`) replaces the inserted support cardinality. The empty case is `component_card_empty`, including a polygon with no crossings.

Singleton children remain counted as actual quotient components: each child list contains its endpoint even when its filtered arc is empty, and SameCycle includes reflexivity. Nothing here replaces a singleton by an empty permutation support. General geometric realization, corner regularity, full visit noncrossing, actual coefficient/state-sum transport and the main corner soft/wall goals remain outside this count packet.
