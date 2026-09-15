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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierInsertOrbits.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- For a fresh actual selected crossing, an explicit inherited-order invariant
and same-current-component premise give the two exact ambient child orbits and
their successor actions. The original rotation and filtered child lists are constructed. -/
theorem smoothingSuccessor_insert_child_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v))) :
    ∃ (k : ℕ) (A B : List (Mark P)),
      (markList hn hP).rotate k = Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B) ∧
      let q := owner hn hP T (Sum.inr v)
      let AL := A.filter (fun m => decide (owner hn hP T m = q))
      let BL := B.filter (fun m => decide (owner hn hP T m = q))
      (Sum.inr v :: BL).Nodup ∧ (Sum.inr (visitTwin v) :: AL).Nodup ∧
      (Sum.inr v :: BL).Disjoint (Sum.inr (visitTwin v) :: AL) ∧
      (∀ m : Mark P, owner hn hP (insert v.1 T) m =
          owner hn hP (insert v.1 T) (Sum.inr v) ↔ m ∈ Sum.inr v :: BL) ∧
      (∀ m : Mark P, owner hn hP (insert v.1 T) m =
          owner hn hP (insert v.1 T) (Sum.inr (visitTwin v)) ↔
          m ∈ Sum.inr (visitTwin v) :: AL) ∧
      (∀ m : Mark P, m ∈ Sum.inr v :: BL →
        smoothingSuccessor hn hP (insert v.1 T) m = (Sum.inr v :: BL).formPerm m) ∧
      (∀ m : Mark P, m ∈ Sum.inr (visitTwin v) :: AL →
        smoothingSuccessor hn hP (insert v.1 T) m =
          (Sum.inr (visitTwin v) :: AL).formPerm m) := by
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  let q := owner hn hP T a
  have hab : a ≠ b := fun he => (visitTwin_ne v).symm (Sum.inr.inj he)
  obtain ⟨k, A, B, hrot, hL, hN, hmem, he⟩ :=
    componentCycle_current_split_data hn hP T hI q a b hab rfl hc.symm
  let AL := A.filter (fun m => decide (owner hn hP T m = q))
  let BL := B.filter (fun m => decide (owner hn hP T m = q))
  have hdata := splitList_child_data a b AL BL hN
  refine ⟨k, A, B, hrot, hdata.1, hdata.2.1, hdata.2.2, ?_, ?_, ?_, ?_⟩
  · intro m
    rw [owner_eq_iff, Equiv.Perm.sameCycle_comm, smoothingSuccessor_insert hn hP T v hv]
    exact splitList_ambient_left_sameCycle_iff (smoothingSuccessor hn hP T)
      a b AL BL hN he m
  · intro m
    rw [owner_eq_iff, Equiv.Perm.sameCycle_comm, smoothingSuccessor_insert hn hP T v hv]
    exact splitList_ambient_right_sameCycle_iff (smoothingSuccessor hn hP T)
      a b AL BL hN he m
  · intro m hm
    rw [smoothingSuccessor_insert hn hP T v hv]
    exact splitList_ambient_left_apply (smoothingSuccessor hn hP T)
      a b AL BL hN he m hm
  · intro m hm
    rw [smoothingSuccessor_insert hn hP T v hv]
    exact splitList_ambient_right_apply (smoothingSuccessor hn hP T)
      a b AL BL hN he m hm

/-- An unaffected old owner block remains exactly one new orbit, with no new
outside marks. Both directions use proved invariant-set orbit transport. -/
theorem owner_insert_iff_of_unaffected (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v))
    (m : Mark P) (hm : owner hn hP T m = q) (z : Mark P) :
    owner hn hP (insert v.1 T) z = owner hn hP (insert v.1 T) m ↔
      owner hn hP T z = q := by
  have ht := sameCycle_congr_of_eqOn_bijOn
    (smoothingSuccessor hn hP T) (smoothingSuccessor hn hP (insert v.1 T))
    {x | owner hn hP T x = q} (smoothingSuccessor_bijOn_owner hn hP T q)
    (smoothingSuccessor_insert_eqOn_owner hn hP T v hv hc q hq).symm m hm z
  constructor
  · intro hz
    have hi := (owner_eq_iff hn hP (insert v.1 T) m z).mp hz.symm
    have ho := (owner_eq_iff hn hP T m z).mpr (ht.mp hi)
    exact ho.symm.trans hm
  · intro hz
    have ho := (owner_eq_iff hn hP T m z).mp (hm.trans hz.symm)
    exact ((owner_eq_iff hn hP (insert v.1 T) m z).mpr (ht.mpr ho)).symm

/-- The actual inherited cycle of an unaffected component is unchanged, since
its new owner filter is pointwise the same original-circle predicate. -/
theorem componentCycle_insert_unaffected (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v))
    (m : Mark P) (hm : owner hn hP T m = q) :
    componentCycle hn hP (insert v.1 T) (owner hn hP (insert v.1 T) m) =
      componentCycle hn hP T q := by
  unfold componentCycle
  apply congrArg (fun p : Mark P → Bool => (markCycle hn hP).filter p)
  funext z
  exact decide_eq_decide.mpr (owner_insert_iff_of_unaffected hn hP T v hv hc q hq m hm z)

end
end SM.Carrier
