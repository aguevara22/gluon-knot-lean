# Ambient transport after checkpoint 100 — 2026-09-12

Read-only analysis by `/root/spanning_gates`; no Lean kernel, proof-candidate edit, source acceptance, stronger fidelity approval or integration approval. The proposed declarations below have not been implemented or checked.

The smallest reusable missing result is orbit transport for two ambient permutations agreeing on one invariant bijective set. Only one restriction's bijectivity must be assumed; the other follows from pointwise agreement. There is no need for ambient finiteness, decidable equality, a nontrivial cycle, or hypotheses describing behavior outside the set.

A precise proposed interface is:

```lean
theorem sameCycle_congr_of_eqOn_bijOn
    {α : Type*} (f g : Equiv.Perm α) (U : Set α)
    (hU : Set.BijOn f U U) (he : Set.EqOn f g U)
    (x : α) (hx : x ∈ U) (y : α) :
    g.SameCycle x y ↔ f.SameCycle x y
```

Specification (1). Here `y` is unrestricted: the conclusion therefore rules out reaching an outside point as well as transferring connectivity inside `U`. Mere `EqOn` without closure is insufficient because inverse iterations could leave the agreement set. `BijOn`, rather than a new finiteness premise, supplies the needed two-sided closure. This is a generic local transport helper, not the actual independent-support induction.

The exact pinned Mathlib route is short. All paths below are relative to `work/lean/.lake/packages/mathlib/Mathlib/`, at pin `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

| API | Role |
|---|---|
| `Set.BijOn.congr`, `Data/Set/Function.lean:661` | Derive `hg : Set.BijOn g U U` from `hU` and `he`. |
| `Set.BijOn.perm_inv`, `GroupTheory/Perm/Basic.lean:55` | Derive inverse closure for each restriction. Together with forward `mapsTo`, obtain `f z ∈ U ↔ z ∈ U` and the analogous iff for `g`. |
| `Equiv.Perm.subtypePerm` and `subtypePerm_apply`, `Algebra/Group/End.lean:367,374` | Construct both permutations on the same subtype `U`. `Equiv.ext` and `Subtype.ext` turn `he` into equality of these restricted permutations. No supplied inverse map is needed. |
| `Equiv.Perm.sameCycle_subtypePerm`, `GroupTheory/Perm/Cycle/Basic.lean:169` | Transfer orbit relations through the two subtype restrictions once both endpoints lie in `U`. |
| `Set.BijOn.perm_zpow`, `GroupTheory/Perm/Basic.lean:64` | In each direction of Specification (1), the given integer-power witness and `hx` show the unrestricted endpoint `y` belongs to `U`, permitting the subtype argument. |

A directly derived convenience result is `f.IsCycleOn U → Set.EqOn f g U → g.IsCycleOn U`: transfer the bijection by `BijOn.congr` and connectivity by Specification (1). Conversely, the orbit characterization can be combined with existing exact local orbit iff statements without introducing this convenience theorem. The relevant existing definitions are `Equiv.Perm.IsCycleOn` (`Cycle/Basic.lean:659`) and `IsCycleOn.range_zpow` (`:798`), both valid for singleton sets.

Observed candidate status at the read was: `CarrierSplitList` passed root 33822, `CarrierSortedArcLists` passed 43464, `CarrierFilteredCycles` passed 72620, `CarrierMarkedArcLists` passed 74734, and `CarrierOrbitRefinement` passed 11497. Their result receipts were present with exit 0. `CarrierInheritedOrder.body.lean` was inspected as a draft; no result receipt was present then. This note does not turn that draft into an accepted dependency or claim its current proof repairs succeeded.

The current actual inputs are now precise:

- `SM.Carrier.componentCycle` in `CarrierFilteredCycles.body.lean` is the original `markCycle` filtered by actual owner. `mem_componentCycle`, `componentCycle_nodup`, `componentCycle_nonempty`, and `componentCycle_eq_filtered_splitList` give its exact marked set and a literal filtered split representative. They do not assert successor compatibility.
- The `CarrierInheritedOrder` draft defines `InheritsMarkOrder` by the actual filtered cycle's `next` agreeing with the current smoothed successor, and `inheritsMarkOrder_iff_formPerm` exposes exactly the pointwise equality needed here. Its `filter_splitList_left/right` compute the two node filters, including the right child's cyclic rotation. The empty and singleton invariant proofs in that draft are limited to those cases.
- `markList_filter_left_iff/right_iff` in `CarrierMarkedArcLists.body.lean` identifies filtered slices with physical traversal arcs and old-owner equality. `independent_twin_same_filtered_slice` puts a remaining pair into one filtered slice **when its current-owner equalities are supplied**. Those equalities remain the second induction invariant, not a consequence of original noninterlacement alone.

For one insert step, use `fT := smoothingSuccessor hn hP T`, a fresh actual crossing visit `v`, and endpoints `a := Sum.inr v`, `b := Sum.inr (visitTwin v)`. Assume the induction hypotheses `InheritsMarkOrder ... T` and that these endpoints are in one current component `q0`. The latter must come from the simultaneous remaining-pair invariant. `componentCycle_eq_filtered_splitList` constructs:

```lean
L := a :: (A ++ b :: B)
```

Specification (2). Here `A,B` are the original rotated arcs filtered by **old** owner `q0`. Exact membership is `m ∈ L ↔ owner T m = q0`, and `L.Nodup` follows from the filtered-cycle Nodup. Applying `inheritsMarkOrder_iff_formPerm` to this literal representative gives `Set.EqOn L.formPerm fT {m | m ∈ L}`. This is equality on the one current component, not equality of whole ambient permutations and not a replacement of `fT` by the original successor.

Let `tau := Equiv.swap a b`, `p := L.formPerm * tau`, and `G := fT * tau`. `SM.Carrier.smoothingSuccessor_insert` in `CarrierSingleSwitch.body.lean` identifies `G` with the actual inserted successor. Since swapping the two displayed endpoints preserves membership in `L`, the preceding old equality implies `Set.EqOn p G {m | m ∈ L}`. Its proof is the three cases `m=a`, `m=b`, and neither, using `Equiv.Perm.mul_apply` and swap evaluation; no order or orbit premise is added.

Now restrict this equality to each child set `UL := {m | m ∈ a :: B}` and `UR := {m | m ∈ b :: A}`. The checked `splitList_left_isCycleOn/right_isCycleOn` supply `Set.BijOn p UL UL` and `Set.BijOn p UR UR`. Specification (1), followed by `splitList_left_sameCycle_iff/right_sameCycle_iff`, gives the exact ambient conclusions:

```lean
G.SameCycle a m ↔ m ∈ a :: B
G.SameCycle b m ↔ m ∈ b :: A
```

Specification (3). These hold for every ambient mark, hence exclude all outside old-component marks and prove endpoint separation. Empty `A` or `B` remains allowed. No separate assumed neighbor map, supplied cycle equivalence, or full-current-orbit enumeration is used.

For every old component `q ≠ q0`, neither endpoint belongs to its marked set. `smoothingSuccessor_insert_other` gives pointwise agreement between `fT` and `G` there. That set is an actual `fT` orbit, so it is bijectively invariant; Specification (1) proves its whole orbit relation is unchanged. This supplies the reverse direction missing from refinement alone and will show that every unaffected `componentForgetSwitch` fiber is a singleton.

Specification (3) converts new owner predicates to child membership. Use the original-circle filter definition, old-owner restriction, `Cycle.filter_filter`, and the draft's `filter_splitList_left/right` to identify the two new actual `componentCycle`s with `(a :: B)` and `(b :: A)` as cycles. The ambient successor agrees there with the respective child `formPerm`, by `splitList_identity` and disjointness. These are exactly the formPerm equalities required by the new `InheritsMarkOrder`. Unaffected filtered cycles follow from unchanged owner blocks. This ownership-to-filter step still needs implementation; Specification (1) alone is not the entire induction step.

The smallest next packet can therefore contain Specification (1), its optional `IsCycleOn` corollary, and a generic split-list specialization deriving the two exact ambient orbit iff statements from only `L.Nodup` and `Set.EqOn L.formPerm fT {m | m ∈ L}`. Root can then instantiate it with the actual filtered component and complete the owner-filter identities. Preserve explicit actual freshness and same-current-component hypotheses until the simultaneous independence induction discharges them. Exact plus-one fibers, the full independent-support invariant, carrier geometry, rotation, named-record/coefficient transport, and the corner soft/wall laws remain further work.
