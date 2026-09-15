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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierPendingPairs.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Every selected crossing still awaiting processing has both actual visits
in one current successor component. This invariant refers to current owners. -/
def PendingPairsTogether (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S T : Finset (Crossing P)) : Prop :=
  ∀ w : Visit P, w.1 ∈ S → w.1 ∉ T →
    owner hn hP T (Sum.inr w) = owner hn hP T (Sum.inr (visitTwin w))

/-- Before any reconnection all marks lie in the single original component,
so every pending pair lies together, without an independence assumption. -/
theorem pendingPairsTogether_empty (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) :
    PendingPairsTogether hn hP S ∅ := by
  intro w _ _
  exact (component_empty_subsingleton hn hP).elim _ _

/-- Inserting a fresh selected crossing preserves current-owner equality for
every other pending selected pair. An unaffected owner block is unchanged.
Inside the affected block, independence puts the pair in one actual physical
arc, and the checked filtered child classification gives one new owner. -/
theorem pendingPairsTogether_insert (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (hPending : PendingPairsTogether hn hP S T)
    (v : Visit P) (hvS : v.1 ∈ S) (hv : v.1 ∉ T) :
    PendingPairsTogether hn hP S (insert v.1 T) := by
  intro w hwS hw
  have hwT : w.1 ∉ T := fun hwT => hw (Finset.mem_insert_of_mem hwT)
  have hvw : v.1 ≠ w.1 := by
    intro he
    apply hw
    rw [← he]
    exact Finset.mem_insert_self _ _
  have hc := hPending v hvS hv
  have hwt := hPending w hwS hwT
  by_cases hq : owner hn hP T (Sum.inr w) = owner hn hP T (Sum.inr v)
  · obtain ⟨k, A, B, hrot, hNLeft, hNRight, hdisjoint,
      hleft, hright, hactLeft, hactRight⟩ :=
      smoothingSuccessor_insert_child_data hn hP T hI v hv hc
    have hqt : owner hn hP T (Sum.inr (visitTwin w)) =
        owner hn hP T (Sum.inr v) := hwt.symm.trans hq
    rcases independent_twin_same_filtered_slice hn hP hS v w hvS hwS hvw
      T (owner hn hP T (Sum.inr v)) hq hqt k A B hrot with ha | hb
    · exact ((hright (Sum.inr w)).mpr
        (List.mem_cons_of_mem _ ha.1)).trans
        ((hright (Sum.inr (visitTwin w))).mpr
          (List.mem_cons_of_mem _ ha.2)).symm
    · exact ((hleft (Sum.inr w)).mpr
        (List.mem_cons_of_mem _ hb.1)).trans
        ((hleft (Sum.inr (visitTwin w))).mpr
          (List.mem_cons_of_mem _ hb.2)).symm
  · exact ((owner_insert_iff_of_unaffected hn hP T v hv hc
      (owner hn hP T (Sum.inr w)) hq (Sum.inr w) rfl
      (Sum.inr (visitTwin w))).mpr hwt.symm).symm

end
end SM.Carrier
