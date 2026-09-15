import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Set.Function
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import SM.InterlaceSupports
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import SM.CarrierMarks
import SM.CarrierSuccessor
import SM.CarrierVisitTwin
import SM.CarrierSmoothing
import SM.CarrierSingleSwitch
import SM.CarrierOrbitRefinement
import SM.CycleFiltering
import SM.CarrierFilteredCycles
import SM.CarrierCycleList
import SM.CarrierSplitList
import SM.CarrierSingleSupport
import SM.CarrierInheritedOrder
import SM.CarrierCurrentCycle
import SM.CarrierAmbientTransport
import SM.CarrierUnchangedComponent
import SM.CarrierInsertOrbits
import SM.CarrierComponentFibers
import SM.CarrierFiberCard
import SM.CarrierSameArc
import SM.CarrierSortedArcLists
import SM.CarrierMarkedArcLists
import SM.CarrierPendingPairs
import SM.CarrierInheritedInsert
import SM.CarrierIndependentOrder

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierComponentCount.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- A fresh reconnection whose actual incoming marks share one current component
increases the actual successor-orbit quotient count by exactly one. The count
comes from the proved literal fibers of the constructed quotient forget map. -/
theorem component_card_insert (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v))) :
    Fintype.card (Component hn hP (insert v.1 T)) =
      Fintype.card (Component hn hP T) + 1 := by
  refine fintype_card_eq_add_one_of_fiber_cards
    (componentForgetSwitch hn hP T v hv ((owner_eq_iff hn hP T _ _).mp hc))
    (owner hn hP T (Sum.inr v)) ?_ ?_
  · obtain ⟨hne, hfiber⟩ := componentForgetSwitch_fiber_affected hn hP T hI v hv hc
    exact (congrArg Finset.card hfiber).trans (Finset.card_pair hne)
  · intro q hq
    obtain ⟨m, hm⟩ := owner_surjective hn hP T q
    exact (congrArg Finset.card
      (componentForgetSwitch_fiber_unaffected hn hP T v hv hc q hq m hm)).trans
        (Finset.card_singleton _)

/-- Every processed subset of an actual independent support has one more
successor-orbit component than processed crossings. Current-order and owner
premises for the count step are supplied by the checked simultaneous induction. -/
theorem component_card_independent_partial (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (T : Finset (Crossing P)) (hTS : T ⊆ S) :
    Fintype.card (Component hn hP T) = T.card + 1 := by
  revert hTS
  induction T using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.card_empty, Nat.zero_add] using component_card_empty hn hP
  | @insert c T hc ih =>
    intro hTS
    have hcS : c ∈ S := hTS (Finset.mem_insert_self c T)
    have hTS' : T ⊆ S := fun z hz => hTS (Finset.mem_insert_of_mem hz)
    obtain ⟨hI, hPending⟩ := independent_partial_invariants hn hP hS T hTS'
    obtain ⟨i, j, hij⟩ := crossing_visits_exist c
    let v : Visit P := ⟨c, i⟩
    have hvS : v.1 ∈ S := hcS
    have hv : v.1 ∉ T := hc
    have hsame := hPending v hvS hv
    have hstep := component_card_insert hn hP T hI v hv hsame
    change Fintype.card (Component hn hP (insert c T)) =
      Fintype.card (Component hn hP T) + 1 at hstep
    rw [hstep, ih hTS', Finset.card_insert_of_notMem hc]

/-- An actual independent support has exactly its cardinality plus one actual
successor-orbit components. Empty support and singleton components are included. -/
theorem component_card_independent (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    Fintype.card (Component hn hP S) = S.card + 1 :=
  component_card_independent_partial hn hP hS S (Finset.Subset.refl S)

/-- The finite successor model satisfies all three combinatorial conclusions:
exact count, inherited marked order and separation of every selected twin pair.
Geometric realization of these orbit components remains a separate obligation. -/
theorem independent_successor_components (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    Fintype.card (Component hn hP S) = S.card + 1 ∧
      InheritsMarkOrder hn hP S ∧
      ∀ v : Visit P, v.1 ∈ S →
        owner hn hP S (Sum.inr v) ≠ owner hn hP S (Sum.inr (visitTwin v)) :=
  ⟨component_card_independent hn hP hS, independent_inheritsMarkOrder hn hP hS,
    fun v hv => independent_selected_pair_owners_ne hn hP hS v hv⟩

end
end SM.Carrier
